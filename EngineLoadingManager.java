/*
 * Copyright (c) 2014-2017 Incorta. All Rights Reserved.
 *
 * Licensed Material - Property of Incorta.
 */
package com.incorta.gen2;

import static com.incorta.common.Util.printMemory;
import static com.incorta.common.Util.duration;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import com.incorta.common.ResourceManager;
import com.incorta.engine.common.GateKeeper;
import com.incorta.engine.common.QueryContext;
import com.incorta.engine.db.ColumnManager;
import com.incorta.engine.db.DBEngine;
import com.incorta.engine.db.DBEngineServices;
import com.incorta.engine.db.Index.UniqueIndex;
import com.incorta.engine.db.RowSet;
import com.incorta.engine.db.RuntimeModel;
import com.incorta.engine.db.Schema;
import com.incorta.engine.db.SchemaDependancyAnalyzer;
import com.incorta.engine.db.SchemaDependancyAnalyzer.Field;
import com.incorta.engine.db.Table;
import com.incorta.engine.exception.EngineErrorCode.EngineErrorType;
import com.incorta.engine.exception.EngineException;
import com.incorta.engine.exception.EngineMajor;
import com.incorta.engine.exception.EngineMinors;
import com.incorta.engine.exception.EngineMinors.LoadingMinors;
import com.incorta.engine.exception.InternalEngineException;
import com.incorta.engine.metamodel.Path;
import com.incorta.engine.metamodel.SchemaModel.TableDef;
import com.incorta.engine.query.Query;
import com.incorta.engine.query.QueryEngine;
import com.incorta.exception.IncortaException;
import com.incorta.filesystem.File;
import com.incorta.io.FilterRecordSet;
import com.incorta.io.IncortaCrypto;
import com.incorta.io.Parquet;
import com.incorta.io.Record;
import com.incorta.io.Record.ColumnDef;
import com.incorta.io.Record.RecordSet;
import com.incorta.io.Record.Type;
import com.incorta.loader.CommitManager;
import com.incorta.loader.Increment;
import com.incorta.loader.LoadingManager;
import com.incorta.loader.Status;
import com.incorta.parquet.FileInfo;
import com.incorta.parquet.ParquetReader;
import com.incorta.server.Configuration;
import com.incorta.server.ErrorMessage;
import com.incorta.server.ErrorMessages;
import com.incorta.server.StatusLogger;
import com.incorta.server.StatusLogger.Phase;
import com.incorta.store.Array;
import com.incorta.store.Array.OutOfMemoryException;
import com.incorta.store.TableColumn;
import com.incorta.util.ConcurrentService;
import com.incorta.util.FileUtil;
import com.incorta.util.Logger;
import com.incorta.visualization.Layout;

final class EngineLoadingManager implements LoadingManager {

    private static final Logger logger = Logger.getLogger(EngineLoadingManager.class);

    private static final int MAX_REJECTED_ROWS_TO_LOG = 30;

    private final Engine engine;
    private final DBEngine dbEngine;
    private final QueryEngine queryEngine;
    private final Schema schema;
    private final String tableName;
    private final boolean fullLoad;
    private final boolean writeSnapshot;
    private final HashMap<String, RowSet> updatedRowsMap;
    private final List<String> fullLoadTables;
    private final Configuration config;
    private final StatusLogger statusLogger;
    private final QueryContext queryContext;
    private final SchemaDependancyAnalyzer schemaDependancyAnalyzer;

    private ColumnManager.Lock initFieldsLock;
    private ColumnManager.Lock initFieldsLoadLock;
    private GateKeeper.LockRequest lock;
    private boolean init;
    private long extractStart;
    private Map<String, Layout> incortaViewTables;
    
    private final CommitManager commitManager;
    private final Set<String> fullyExtractedOrTransformedTables;
    private final ArrayList<String> tablesWithNewRows;


    EngineLoadingManager(Engine engine, DBEngine dbEngine, CommitManager commitManager, String schemaName, String tableName, boolean fullLoad, List<String> fullLoadTables,
            Set<String> fullyExtractedOrTransformedTables, boolean writeSnapshot, Configuration config, StatusLogger statusLogger) {

        this.engine = engine;
        this.dbEngine = dbEngine;
        this.commitManager = commitManager; 
        this.queryEngine = dbEngine.getQueryEngine();
        this.schema = dbEngine.getSchema(schemaName);
        this.tableName = tableName;
        this.fullLoad = fullLoad;
        this.writeSnapshot = writeSnapshot;
        this.updatedRowsMap = new HashMap<String, RowSet>();
        this.fullLoadTables = fullLoadTables;
        this.fullyExtractedOrTransformedTables = fullyExtractedOrTransformedTables;
        this.config = config;
        this.statusLogger = statusLogger;
        this.queryContext = new QueryContext(dbEngine.getRuntimeModel(), "system");
        this.incortaViewTables = new HashMap<>();
        this.schemaDependancyAnalyzer = new SchemaDependancyAnalyzer(dbEngine.getRuntimeModel());
        this.tablesWithNewRows = new ArrayList<>();
    }

    @Override
    public void init() throws EngineException {

        try {
            if (!engine.isReady()) {
                logger.info("Engine not started yet. Loading of schema [" + schema.getName() + "] will be queued until the engine is ready.");

                do {
                    try {
                        Thread.sleep(2_000);

                    } catch (InterruptedException e) {
                        throw new EngineException("Thread interrupted", EngineMajor.LOADING, EngineMinors.LoadingMinors.INIT,
                                EngineErrorType.ENGINE_THREAD_INTERRUPTED_LOAD, e, schema.getName());
                    }

                } while (!engine.isReady());

                logger.info("Engine started. Loading of schema [" + schema.getName() + "] will start.");
            }

            if (!engine.isValid()) {
                throw new EngineException("Engine is not valid. Loading of schema [" + schema.getName() + "] will not start.", EngineMajor.LOADING,
                        EngineMinors.LoadingMinors.INIT, EngineErrorType.ENGINE_LOADING_INIT_FAILED, schema.getName());
            }

            if (schema.getStatus() != Schema.SCHEMA_LOADING) {
                schema.setStatus(Schema.SCHEMA_LOADING, engine.getSnapshotsPath());
            }

            ErrorMessages errorMessages = new ErrorMessages();
            lock = dbEngine.preLoadSchema(schema, tableName, !fullLoad, fullLoadTables, errorMessages);
            boolean readFromParquet;
            Set<Field> toReadFields = new HashSet<>();
            Set<Field> toLockFields = new HashSet<>();

            if (tableName == null) { // Schema Load
                for (Table table : schema.getTables()) {
                    // table has load filter or Encrypted column
                    readFromParquet = !table.getModel().hasLoadFilter() && !table.isEncrypted();
                    handleTableLoad(readFromParquet, toReadFields, toLockFields, table.getName());
                }
                
            } else {
                // Table Load
                Table table = dbEngine.getTable(tableName);
                // table has load filter or encrypted
                readFromParquet = !table.getModel().hasLoadFilter() && !table.isEncrypted();
                handleTableLoad(readFromParquet, toReadFields, toLockFields, tableName);
                handleTableLoad(readFromParquet, toReadFields, toLockFields, tableName);
            }

            if (!toReadFields.isEmpty()) {
                
                setFieldsReadFromTemp(toReadFields);
                
                logger.info("Requesting columns in init for loading schema: " + schema.getName() + " ,Table: " + tableName + "are "
                        + Arrays.toString(toReadFields.toArray()));
                try {
                    initFieldsLoadLock = dbEngine.getColumnManager().requestEvictableFields(toReadFields, errorMessages);
                } catch (InternalEngineException e) {
                    throw new EngineException("Could not request fields while intializing due to out of memory exception", EngineMajor.LOADING,
                            EngineMinors.LoadingMinors.INIT, e.getErrorType(), e, e.getParams());
                }
            }

            if (!toLockFields.isEmpty()) {
                logger.info("Locking columns in init for loading schema: " + schema.getName() + " ,Table: " + tableName + "are "
                        + Arrays.toString(toLockFields.toArray()));
                initFieldsLock = dbEngine.getColumnManager().lockFields(getFieldNames(toLockFields), errorMessages);
            }

            init = true;

        } catch (OutOfMemoryException | OutOfMemoryError e) {
            throw new EngineException("Failed to request fields to start post load due to out of memory exception", EngineMajor.LOADING,
                    EngineMinors.LoadingMinors.INIT, EngineErrorType.ENGINE_OOM, e);

        } catch (InternalEngineException e) {
            throw new EngineException("Failed to pre load schema " + schema.getName(), EngineMajor.LOADING, LoadingMinors.INIT, e.getErrorType(), e,
                    e.getParams());
            
        } catch (Throwable e) {
            throw new EngineException("Unexpected exception in postload", EngineMajor.LOADING, LoadingMinors.INIT,
                    EngineErrorType.ENGINE_INIT_FAILED_UNEXPECTED, e);
        }
    }

    private void handleTableLoad(boolean readFromParquet, Set<Field> toReadFields, Set<Field> toLockFields, String tableName) {
        if (readFromParquet) {

            // read only primary indices for index calculation in loading phase.
            toReadFields.addAll(schemaDependancyAnalyzer.getPrimaryKeyColumns(schema, tableName));
            toLockFields.addAll(schemaDependancyAnalyzer.getDataColumns(schema, tableName));
            
            if (!fullLoad && !fullLoadTables.contains(tableName)) { // Incremental load table
                toReadFields.addAll(schemaDependancyAnalyzer.getIndexes(schema, tableName));

            } else {
                toLockFields.addAll(schemaDependancyAnalyzer.getIndexes(schema, tableName));
            }

        } else { // read from snapshots
            // lock internal DataColumns + PK'S
            if (fullLoad || fullLoadTables.contains(tableName)) { // full load
                toLockFields.addAll(schemaDependancyAnalyzer.getDataColumns(schema, tableName));
                toLockFields.addAll(schemaDependancyAnalyzer.getIndexes(schema, tableName));

            } else {
                // read internal DataColumns + PK'S
                toReadFields.addAll(schemaDependancyAnalyzer.getDataColumns(schema, tableName));
                // if incremental load, read indexes
                toReadFields.addAll(schemaDependancyAnalyzer.getIndexes(schema, tableName));
            }
        }
    }

    /**
     * FullLoad Inconsistency Issue
     * mark Columns which will be read from Fully extracted/transformed tables
     * so read them from Temp Parquet dir
     */
    private void setFieldsReadFromTemp(Set<Field> toReadFields) {
        for (Field field : toReadFields) {
            String tableName = Path.fullTable(field.getName());
            if (fullyExtractedOrTransformedTables.contains(tableName)) {
                field.setReadFromTemp();
            }
        }
    }
    
    @Override
    public void setStartTime(long time) {
        this.extractStart = time;
    }

    @Override
    public void end(Status status, List<String> errors) throws EngineException {
        if (!engine.isValid())
            return;

        close(initFieldsLoadLock);
        close(initFieldsLock);

        if (!init) {
            logger.error("error in load intialization during the start of postload process");
            close(lock);
            schema.setStatus(status == Status.ERROR ? Schema.SCHEMA_ERROR : Schema.SCHEMA_INTERRUPT, dbEngine.getFileManager().getBaseDir());
            for (String error: errors) schema.addErrorMessage(error);
            return;
        }
        
        ErrorMessages errorMessages = new ErrorMessages();
        printMemory(logger, "Before loading into engine", -1);

        // get affected Incorta view tables
        if (tableName == null) {
            findAllIncortaViewTables();

        } else {
            findRelatedIncortaViewTables(errorMessages);
        }

        String[] errorsArray = errors.toArray(new String[errors.size()]);
        Set<Field> toReadFields = new HashSet<>();
        Set<Field> toLockFields = new HashSet<>();
        Set<Field> relatedFormulas = new HashSet<>();

        try {
            // single table load is always FULL
            if (fullLoad || tableName != null) { // FULL TABLE OR SCHEMA LOAD
                Set<Field> calculatedFields = schemaDependancyAnalyzer.getCalculatedFields(schema, tableName, errorMessages);
                toLockFields.addAll(calculatedFields);

                if (tableName != null) { // for full table load only
                    relatedFormulas.addAll(schemaDependancyAnalyzer.getRelatedFormulaColumns(schema, tableName, false, errorMessages));
                    toLockFields.addAll(relatedFormulas);
                }

                Set<Field> allDependancies = schemaDependancyAnalyzer.getAllDependancies(queryEngine, schema, tableName, errorMessages);
                allDependancies.removeAll(toLockFields);
                toReadFields.addAll(allDependancies);

            } else { // INCREMNTAL LOAD
                toReadFields.addAll(schemaDependancyAnalyzer.getSchemaAliasJoinsWithDependencies(schema, errorMessages));
                for (Table t : schema.getTables()) {
                    Set<Field> calculatedFields = schemaDependancyAnalyzer.getCalculatedFields(schema, t.getName(), errorMessages);
                    if (fullLoadTables.contains(t.getName())) { // FULL LOAD
                        toLockFields.addAll(calculatedFields);

                        Set<Field> allDependancies = schemaDependancyAnalyzer.getAllDependancies(queryEngine, schema, t.getName(), errorMessages);
                        allDependancies.removeAll(toLockFields);
                        toReadFields.addAll(allDependancies);

                    } else { // INCREMNTAL LOAD
                        toReadFields.addAll(calculatedFields);
                        toReadFields.addAll(schemaDependancyAnalyzer.getAllDependancies(queryEngine, schema, t.getName(), errorMessages));
                    }
                }
            }

            setFieldsReadFromTemp(toReadFields);
            
            // we can clear it. But it is not harmful for now to have a double lock as long
            // as all locks will be released together
            logger.info("Requesting columns Before PostLoad of Schema: " + schema.getName() + " ,Table: " + tableName + "are"
                    + Arrays.toString(toReadFields.toArray()));

            logger.info("Requesting Lock only for columns Before PostLoad of Schema: " + schema.getName() + " ,Table: " + tableName + "are"
                    + Arrays.toString(toLockFields.toArray()));

            try (ColumnManager.Lock postLoadFieldsReadLock = dbEngine.getColumnManager().requestEvictableFields(toReadFields, errorMessages);
                    ColumnManager.Lock postLoadFieldsLock = dbEngine.getColumnManager().lockFields(getFieldNames(toLockFields), errorMessages)) {

                clearRelatedFormulaColumns(relatedFormulas);

                // calculate formula & join columns
                dbEngine.postLoad(schema, tableName, extractStart, updatedRowsMap, tablesWithNewRows, !fullLoad, status, init, errorsArray, false, errorMessages);

                // materialize Incorta tables before writing snapshots
                materializeIncortaTables(errorMessages);

                // calculate formula & join columns
                dbEngine.postLoad(schema, tableName, extractStart, updatedRowsMap, tablesWithNewRows, !fullLoad, status, init, errorsArray, true, errorMessages);

                // write snapshots
                Set<String> relatedFormulaNames = new HashSet<>(relatedFormulas.size());
                for (Field formula : relatedFormulas)
                    relatedFormulaNames.add(formula.getName());

                commitSchemaData(relatedFormulaNames, errorMessages); 

                printMemory(logger, "After loading into engine", -1);
            }
            
        } catch (OutOfMemoryException | OutOfMemoryError e) {
            throw new EngineException("Failed to start post load due to out of memory exception", EngineMajor.LOADING,
                    EngineMinors.LoadingMinors.CALCULATIONS, EngineErrorType.ENGINE_OOM, e, e);

        } catch (InternalEngineException e) {
            throw new EngineException("Error while post loading", EngineMajor.LOADING, EngineMinors.LoadingMinors.CALCULATIONS, e.getErrorType(), e,
                    e.getParams());
            
        } catch (EngineException e) {
            throw e;
            
        } catch (Throwable e) {
            throw new EngineException("Unexpected exception in postload", EngineMajor.LOADING, LoadingMinors.CALCULATIONS,
                    EngineErrorType.ENGINE_POSTLOAD_CALCULATION_UNEXPECTED, e);

        } finally {
            // close gate keeper write lock
            close(lock);

            if (updatedRowsMap != null) {
                for (RowSet currentRowSet : updatedRowsMap.values()) {
                    currentRowSet.clear();
                }
            }

            // clear incortaViewTables
            incortaViewTables.clear();
        }
    }

    /**
     * FullLoad & Writing Snapshots Inconsistency Issue
     * 1- write snapshots without Rotation
     * 2- check if compaction finished for fully extracted/transformed tables only
     * 3- commit snapshots files
     * 4- commit fully extracted tables Parquet
     * @throws IOException 
     */
    private void commitSchemaData(Set<String> relatedFormulaNames, ErrorMessages errorMessages) throws EngineException {
        logger.info("Finished postLoading Schema: " + schema.getName() + ", Table: " +  tableName);
        
        // write snapshots ...throw EngineException(WritingSnapshotsError)
        final Set<String> toBeRotated = Collections.synchronizedSet(new HashSet<>());
        dbEngine.writeSnapshots(schema.getName(), writeSnapshot, relatedFormulaNames, (tableName == null), errorMessages, toBeRotated);
        
        // commit ....throw EngineException(CommitDataError)
        try {
            // ensure Compaction finished , check before writing snapshots, to wait in Consistent state
            commitManager.checkCompactionJob();
            
            // commit snapshots
            commitSnapshots(toBeRotated, errorMessages);
            
            // commit full extracted tables parquet
            commitManager.commitFullExtractedTransformedTables();
            
        } catch (Throwable e) {
            throw new EngineException("Error while Commiting Data for schema", EngineMajor.LOADING, LoadingMinors.COMMIT_DATA, EngineErrorType.ENGINE_LOADING_COMMIT_DATA_FAILED, e, schema.getName());
        }
    }
    
    /**
     * commit snapshots...Rotate Snapshots files
     * ContinueOnerror : False....On First Error fail the whole loading job
     * @param toRotate
     * @throws IOException 
     */
    private void commitSnapshots(final Set<String> toBeRotated, ErrorMessages errorMessages) throws Throwable {
        logger.info("Start Committing Snapshots files");
        long t0 = System.currentTimeMillis();
        List<String> toRotateFiles = new ArrayList<String>(toBeRotated);
                
        ResourceManager.getInstance().getColumnsConcurrentService().run("Rotate Snapshot File", false, toRotateFiles.size(), new ConcurrentService.Action<IOException>() {
            @Override
            protected String getName(int index) {
                return toRotateFiles.get(index);
            }

            @Override
            protected void doAction(int index) throws IOException {
                dbEngine.getFileManager().rotate(toRotateFiles.get(index), errorMessages);
            }
        });

        logger.info("Finished Committing Snapshots files in: " + duration(t0));
    }
    
    private void clearRelatedFormulaColumns(Set<Field> relatedFormulas) {
        RuntimeModel runtimeModel = dbEngine.getRuntimeModel();
        for (Field field : relatedFormulas) {
            String tableName = Path.fullTable(field.getName());
            TableColumn col = runtimeModel.getColumn(field.getName());
            Table table = runtimeModel.getTable(tableName);
            if (col == null || table == null)
                continue;
            col.reset(table.size());
        }
    }

    private void close(AutoCloseable lock) {
        try {
            if (lock != null)
                lock.close();
        } catch (Exception e) {
            logger.error("can't release lock");
        }
    }

    // if load schema then get any Incorta view table
    protected void findAllIncortaViewTables() {
        TableDef tableDef;
        for (int index = 0; index < schema.getTableDefCount(); index++) {
            tableDef = schema.getTableDef(index);
            if (tableDef.isIncortaViewTable()) {
                incortaViewTables.put(tableDef.getName(), DBEngineServices.getLayout(
                        engine.getEngineContext(), dbEngine.getRuntimeModel(), tableDef, config.getEngineMaxGroups(), config.getEngineMaxGroupsLimit()));
            }
        }
    }

    protected void findRelatedIncortaViewTables(ErrorMessages errorMessages) {
        TableDef loadedTableDef = getTableDef(tableName);
        if (loadedTableDef == null)
            return;

        incortaViewTables.putAll(DBEngineServices.findRelatedIncortaTable(engine.getEngineContext(), dbEngine.getRuntimeModel(), queryEngine, queryContext, schema, 
                loadedTableDef, config.getEngineMaxGroups(), config.getEngineMaxGroupsLimit(), errorMessages));
    }

    // materialize all Incorta tables
    protected void materializeIncortaTables(ErrorMessages errorMessages) throws EngineException, InternalEngineException {
        for (Entry<String, Layout> incortaViewTable : incortaViewTables.entrySet()) {
            materializeIncortaTable(incortaViewTable.getKey(), incortaViewTable.getValue(), errorMessages);
        }
    }

    // execute query and load results in table identified by passed `tableDef`
    protected void materializeIncortaTable(String tableName, Layout layout, ErrorMessages errorMessages)
            throws InternalEngineException, EngineException {
        long rowsBefore = 0;
        try {
            startLoading(tableName);
            // evaluate sub-queries
            engine.evaluateFilterModelSubqueries(null, layout);
            Table incortaTable = dbEngine.getTable(tableName);
            rowsBefore = incortaTable == null ? 0 : incortaTable.size();
            Query query = layout.getTableQuery(queryEngine);
            long rowsAfter = DBEngineServices.materializeTable(dbEngine.getRuntimeModel(), queryEngine, dbEngine.getSchemaManager(),
                    dbEngine.getColumnManager(), queryContext, query, DBEngineServices.isHierarchical(layout), schema.getName(), tableName,
                    errorMessages);
            endLoading(tableName, rowsBefore, rowsAfter);

        } catch (InternalEngineException e ) {
            EngineException engineException = new EngineException("Failed to materialize incorta table", EngineMajor.LOADING,
                    EngineMinors.LoadingMinors.CALCULATIONS, 
                    e.getErrorType() == EngineErrorType.CONDITION_COMPILER_CHECK_VARIABLES_MISSING ? EngineErrorType.ENGINE_INVALID_INCORTA_TABLE : e.getErrorType(), e.getCause(), 
                    e.getErrorType() == EngineErrorType.CONDITION_COMPILER_CHECK_VARIABLES_MISSING ? null : e.getParams());
            String message = "Failed to materialize table " + tableName + ":\n" + engineException.getMessage();
            logger.error(message);
            endLoading(tableName, rowsBefore, engineException);

        } catch (IncortaException e ) {
            EngineException engineException = new EngineException("Failed to materialize incorta table", EngineMajor.LOADING,
                    EngineMinors.LoadingMinors.CALCULATIONS, EngineErrorType.MATRIALIZE_INCORTA_TABLE_FAILURE, e.getCause());
            String message = "Failed to materialize table " + tableName + ":\n" + engineException.getMessage();
            logger.error(message);
            endLoading(tableName, rowsBefore, engineException);
        } 
    }

    // start loading task for table with name `tableName`
    private void startLoading(String tableName) {
        if (statusLogger.getTask(tableName) == null)
            statusLogger.addTask(tableName);
        statusLogger.start(Phase.Load, tableName);
    }

    // end loading task for table with name `tableName` successfully
    private void endLoading(String tableName, long rowsBefore, long rowsAfter) {
        statusLogger.end(Phase.Load, tableName, true, rowsBefore, rowsAfter, 0, rowsAfter);
    }

    // end loading task for table with name `tableName` with failure
    private void endLoading(String tableName, long rowsBefore, IncortaException exception) {
        statusLogger.setTableError(tableName, new ErrorMessage(exception));
        statusLogger.end(Phase.Load, tableName, false, rowsBefore, 0, 0, 0);
    }

    // find table definition by name
    private TableDef getTableDef(String name) {
        for (int index = 0; index < schema.getTableDefCount(); index++) {
            TableDef tableDef = schema.getTableDef(index);
            if (tableDef.getName().equals(name))
                return tableDef;
        }

        logger.error("Undefined table " + tableName);
        return null;
    }

    @Override
    public void skipTable(String fullTableName, ColumnDef[] columns, boolean incremental, boolean successful, boolean empty) throws EngineException {

        // DO nothing, this is a workaround to bypass the engine limitations. Commit has
        // to be called what so ever!
        // INC-11245: In case of incremental, we must send success = true even if
        // extraction failed,
        // because the engine does not need to rollback.

        // getStore(dbEngine.getTable(fullTableName), columns,
        // incremental).close(incremental || successful);
        ErrorMessages errorMessages = new ErrorMessages();

        boolean success = incremental || successful;
        Table table = dbEngine.getTable(fullTableName);

        try (ColumnManager.Lock lock = preLoadTable(table, incremental, errorMessages)) {
             dbEngine.commit(table, success, errorMessages);
        }
        if (success && incremental) addUpdatedRows(table.getName(), new RowSet(table.size()));
//        if (!errorMessages.hasErrors()) {
//            throw new EngineException("failed to load table "+ fullTableName + "due to errors in preload and commit" , EngineMajor.LOADING, EngineMinors.LoadingMinors.LOAD, EngineErrorType.ENGINE_LOADING_SKIPTABLE_FAILED, fullTableName);
//        } // FIXME: INC-19035
    }

    @Override
    public LoadingResult loadTableIncrements(String fullTableName, ColumnDef[] columns, boolean incremental, String filter,
            List<Increment> increments) throws EngineException {

        ErrorMessages errorMessages = new ErrorMessages();
        Table table = dbEngine.getTable(fullTableName);
        if (table == null) {
            logger.warn("Table [" + fullTableName + "] does not exist");
            throw new EngineException("Table cannot be null " + fullTableName, EngineMajor.LOADING, EngineMinors.LoadingMinors.LOAD,
                    EngineErrorType.ENGINE_TABLE_NOT_FOUND, fullTableName);
        }

        boolean success = true;
        long initialSize = table.size();
        long[] result = null;
        RowSet updated = null;

        File[] files = increments.stream().map(i -> FileUtil.newInstance(i.getLocation())).toArray(File[]::new);

        try {
            ParquetReader parquetReader = new ParquetReader(files);

            // ColumnManager.Lock lock = preLoadTable(table, incremental);
            updated = incremental ? new RowSet(initialSize + parquetReader.getDistinctRowsCount()) : null;

            boolean hasEncryption = false;
            for (ColumnDef c : columns) {
                if (c.isEncrypted()) {
                    hasEncryption = true;
                    break;
                }
            }

            logger.info(
                    "Load Table " + fullTableName + " currentSize: " + initialSize + " with Increments: " + Arrays.toString(increments.toArray()));

            if (filter == null && !hasEncryption) { // can use fast parquet reader
                if (table.getPrimaryKeyIndex() == null || parquetReader.offsetsExists()) {
                    result = loadTableByColumn(table, columns, parquetReader, updated, initialSize, incremental);
                    logger.info("Finish Loading Table " + fullTableName + " ByColumn currentSize: " + table.size());

                    if (!increments.isEmpty()) {
                        // update table last Increment
                        Increment lastIncrement = increments.get(increments.size() - 1);
                        table.setLastIncrementTimestamp(lastIncrement.getTimestamp());
                        table.setLastIncrementUUID(lastIncrement.getUuid());
                        logger.info("Update Table " + fullTableName + " with Last Increment: " + lastIncrement.toString());
                        dbEngine.getColumnManager().updateLastIncrement(table.getName(), table.getLastIncrementTimestamp(),
                                table.getLastIncrementUUID());
                    }
                }
            }

            if (result == null) {
                result = loadTableByRow(table, columns, files, updated, initialSize, filter);
                logger.info("Finish Loading Table " + fullTableName + " ByRow currentSize: " + table.size());
            }

        } catch (OutOfMemoryException | OutOfMemoryError e) {
            success = false;
            throw e;

        } catch (EngineException e) {
            logger.error(e.getDetailedMessage(), e.getMessage());
            success = false;
            throw e;

        } catch (IOException e) {
            success = false;
            throw new EngineException("IO Exception while requesting a fast parquet reader for table " + table.getName(), EngineMajor.LOADING,
                    EngineMinors.LoadingMinors.LOAD, EngineErrorType.ENGINE_LOAD_REQUEST_PARQUET_READER, e, table.getName());

        } catch (Throwable e) {
            success = false;
            throw new EngineException("Unexpected Exception happened while loading table " + table.getName(), EngineMajor.LOADING,
                    EngineMinors.LoadingMinors.LOAD, EngineErrorType.ENGINE_LOAD_UNKOWN_EXCEPTION, e, table.getName());
            
        } finally {
            // TODO edit commit handle table load failure in case of parquet
            dbEngine.commit(table, success, errorMessages);
            if (success && updated != null) {
                addUpdatedRows(table.getName(), updated);
                
            } else if (updated != null) {
                updated.clear();
            }
        }

        if (table.size() > initialSize) {
            synchronized (tablesWithNewRows) { tablesWithNewRows.add(table.getName()); }
        }
        
        return new LoadingResult(initialSize, table.size(), result[0], result[1]);
    }

    private long[] loadTableByColumn(Table table, ColumnDef[] columns, ParquetReader parquetReader, RowSet updatedSet, long initialSize,
            boolean incremental) throws EngineException {
        try {
            // get only InMemory table Columns
            List<TableColumn> tableColumns = new ArrayList<>();
            for (ColumnDef col : columns) {
                TableColumn tableColumn = (TableColumn) table.getColumn(col.getName());
                if (tableColumn != null && tableColumn.isInMemory())
                    tableColumns.add(tableColumn);
            }
            TableColumn[] inMemoryColumns = tableColumns.toArray(new TableColumn[tableColumns.size()]);

            if (inMemoryColumns.length == 0) {
                // So there is no PK, incase of full load: old table size = 0
                table.setSize(table.size() + parquetReader.getRowsCount());

            } else {
                /*
                 * full load: No need to load any thing columns already loaded in memory with
                 * full load parquet
                 */

                if (incremental) {
                    TableColumn.readFromParquet(inMemoryColumns, parquetReader);
                }
                // set table.size = size of any column in memory
                table.setSize(inMemoryColumns[0].size());
            }

            UniqueIndex index = table.getPrimaryKeyIndex();
            if (index != null) {
                index.update();
                index.setInMemory(true); // FIXME Remove this from here

                if (updatedSet != null) {
                    for (FileInfo f : parquetReader.getFilesInfo()) {
                        for (long r : f.readOffsets()) {
                            if (r < initialSize)
                                updatedSet.addRow(r);
                        }
                    }
                }
            }
            return new long[] { parquetReader.getRowsCount(), 0 };

        } catch (InternalEngineException e) {
            throw new EngineException("Out of memory exception while reading columns increments from parquet for table " + table.getName(),
                    EngineMajor.LOADING, EngineMinors.LoadingMinors.LOAD, e.getErrorType(), e, e.getParams());

        } catch (IOException e) {
            throw new EngineException("IO exception while reading columns increments from parquet for table " + table.getName(), EngineMajor.LOADING,
                    EngineMinors.LoadingMinors.LOAD, EngineErrorType.ENGINE_LOAD_BY_COLUMNS, e, table.getName());

        }
    }

    private ColumnManager.Lock preLoadTable(Table table, boolean incremental, ErrorMessages errorMessages) throws EngineException {
        try {
            return dbEngine.preLoadTable(table, incremental, errorMessages);

        } catch (InternalEngineException e) {
            // FIXME Handle exception
            throw new EngineException("failed to preload table " + table.getName() + " due to out of memory", EngineMajor.LOADING,
                    EngineMinors.LoadingMinors.LOAD, e.getErrorType(), e, table.getName());
        }
    }

    private void addUpdatedRows(String tableName, RowSet updatedRows) {
        synchronized (updatedRowsMap) {
            updatedRowsMap.put(tableName, updatedRows);
        }
    }

    private long[] loadTableByRow(Table table, ColumnDef[] columns, File[] files, RowSet updatedSet, long initialSize, String filter)
            throws Exception {

        long row = 0;
        long errorCount = 0;

        try (RecordSet rs = read(columns, filter, files)) {
            EngineDataStore store = new EngineDataStore(table, columns, updatedSet, initialSize);

            for (Record r; (!Thread.interrupted()) && (r = rs.next()) != null;) {
                try {
                    store.write(r);
                    
                } catch (OutOfMemoryException | OutOfMemoryError e) {
                    logger.error("Out Of Memory while loading row #: " + row + " -> ", e.getCause());
                    throw e;

                } catch (Throwable e) {
                    if (errorCount++ <= MAX_REJECTED_ROWS_TO_LOG) {
                        String msg = e.getMessage() != null ? (e.getClass().getSimpleName() + " : " + e.getMessage()) : e.getClass().getSimpleName();
                        logger.error("Error in row #: " + row + " -> " + msg, e);
                    }
                }
                row++;
            }

        }

        // FIXME Remove this from here
        // set columns in memory to be used in Table.commit
        for (int col = 0; col < table.getBaseColumnCount(); col++) {
            TableColumn tc = (TableColumn) table.getColumn(col);
            tc.setInMemory(true);
        }

        if (table.getPrimaryKeyIndex() != null) {
            table.getPrimaryKeyIndex().setInMemory(true);
        }

        return new long[] { row, errorCount };
    }

    private RecordSet read(ColumnDef[] columns, String filter, File[] files) throws EngineException {
        RecordSet rs;
        try {
            rs = Parquet.readAll(columns, new IncortaCrypto(), files);
            if (filter != null)
                rs = FilterRecordSet.create(rs, filter);
            return rs;
        } catch (IOException e) {
            throw new EngineException("IO exception while reading columns from parquet for loading", EngineMajor.LOADING,
                    EngineMinors.LoadingMinors.LOAD, EngineErrorType.ENGINE_LOADING_IO_EXCEPTION, e, Arrays.toString(columns));
        }

    }

    private Collection<String> getFieldNames(Collection<Field> fields) {
        return fields.stream().map(f -> f.getName()).collect(Collectors.toList());
    }

    private static final class EngineDataStore {

        private final Table table;
        private final UniqueIndex index;
        private final RowSet updatedSet;
        private final long initialSize;
        private final FieldWriter[] writers;

        private long newRowsCount;

        EngineDataStore(Table table, ColumnDef[] schema, RowSet updatedSet, long initialSize) {
            this.table = table;
            this.index = table.getPrimaryKeyIndex();
            this.updatedSet = updatedSet;
            this.initialSize = initialSize;
            this.writers = createWriters(table, schema);
        }

        void write(Record record) throws EngineException, InternalEngineException {
                final FieldWriter[] writers = this.writers;

                if (index == null) {
                    long curRow = table.addRow();

                    for (int i = 0, len = writers.length; i < len; i++) {
                        writers[i].write(record, table, curRow);
                    }

                } else {
                    long curRow = index.find(record.getKey());
                    long pos = -1;

                    if (curRow < 0) {
                        pos = -curRow - 1;
                        curRow = table.addRow();
                        newRowsCount++;

                    } else if (curRow < initialSize) {
                        updatedSet.addRow(curRow);
                    }

                    for (int i = 0, len = writers.length; i < len; i++) {
                        writers[i].write(record, table, curRow);
                    }

                    if (pos >= 0)
                        index.add((int) pos, curRow);
                }

            if (newRowsCount % 10_000 == 0 && !ResourceManager.getInstance().isSufficientMemory()) {
                throw new EngineException("Low memory excpetion while loading", EngineMajor.LOADING, EngineMinors.LoadingMinors.LOAD,
                        EngineErrorType.ENGINE_LOW_MEMORY_EXCEPTION, Array.getNativeMemoryUsed() / Math.pow(2, 30),
                        ResourceManager.getInstance().getMaxOffHeapMemory() / Math.pow(2, 30));
            }
        }
    }

    private static FieldWriter[] createWriters(Table table, ColumnDef[] schema) {

        FieldWriter[] writers = new FieldWriter[schema.length];

        Map<String, Integer> columnIndices = new HashMap<>();
        for (int index = 0; index < table.getColumnCount(); index++) {
            columnIndices.put(table.getColumnName(index), index);
        }

        int i = 0;
        for (ColumnDef c : schema) {
            int source = i;
            writers[i++] = createWriter(c.getType(), c.getName(), source, columnIndices.get(c.getName()));
        }

        return writers;
    }

    private abstract static class FieldWriter {

        private final int source;
        private final int target;

        FieldWriter(int source, int target) {
            this.source = source;
            this.target = target;
        }

        final void write(Record record, Table table, long row) {

            if (record.isNull(source)) {
                table.setNull(row, target);

            } else {
                write(record, table, row, source, target);
            }
        }

        abstract void write(Record record, Table table, long row, int source, int target);
    }

    private static FieldWriter createWriter(Type type, String name, int source, int target) {

        switch (type) {

        case BOOL:
            return new FieldWriter(source, target) {

                @Override
                void write(Record record, Table table, long row, int source, int target) {
                }
            };

        case INT:
            return new FieldWriter(source, target) {

                @Override
                void write(Record record, Table table, long row, int source, int target) {
                    table.setInt(row, target, record.getInt(source));
                }
            };

        case LONG:
            return new FieldWriter(source, target) {

                @Override
                void write(Record record, Table table, long row, int source, int target) {
                    table.setLong(row, target, record.getLong(source));
                }
            };

        case DOUBLE:
            return new FieldWriter(source, target) {

                @Override
                void write(Record record, Table table, long row, int source, int target) {
                    table.setDouble(row, target, record.getDouble(source));
                }
            };

        case STRING:
        case TEXT:
            return new FieldWriter(source, target) {

                @Override
                void write(Record record, Table table, long row, int source, int target) {
                    String value = record.getString(source);
                    if (value != null) {
                        table.setString(row, target, value.trim());
                    }
                }
            };

        case DATE:
            return new FieldWriter(source, target) {

                @Override
                void write(Record record, Table table, long row, int source, int target) {
                    table.setLong(row, target, record.getDate(source));
                }
            };

        case TIMESTAMP:
            return new FieldWriter(source, target) {

                @Override
                void write(Record record, Table table, long row, int source, int target) {
                    table.setLong(row, target, record.getTimestamp(source));
                }
            };

        default:
            throw new IllegalStateException("Invalid type: " + type + " for column: " + name);
        }
    }
}
