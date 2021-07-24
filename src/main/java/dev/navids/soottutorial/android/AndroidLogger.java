
package dev.navids.soottutorial.android;

import soot.*;
import soot.jimple.*;
import soot.jimple.internal.*;

import java.io.File;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.HashSet;
import java.util.HashMap;

import java.util.concurrent.locks.*;

public class AndroidLogger {

    private final static String USER_HOME = System.getProperty("user.home");
    private static String androidJar = USER_HOME + "/Documents/android/platforms";
    private static HashSet<String> generatedFunctionNames = new HashSet<String>();
    static String androidDemoPath = System.getProperty("user.dir") + File.separator + "demo" + File.separator + "Android";
    static String apkPath = androidDemoPath + File.separator + "/calc.apk";
    static String outputPath = androidDemoPath + File.separator + "/Instrumented";

    static ReentrantLock lock = new ReentrantLock();

    public static void main(String[] args){
        if(System.getenv().containsKey("ANDROID_HOME"))
            androidJar = System.getenv("ANDROID_HOME")+ File.separator+"platforms";
        // Clean the outputPath
        final File[] files = (new File(outputPath)).listFiles();
        if (files != null && files.length > 0) {
            Arrays.asList(files).forEach(File::delete);
        }
        // Initialize Soot
        InstrumentUtil.setupSoot(androidJar, apkPath, outputPath);
        // Find the package name of the APK
        String packageName = AndroidUtil.getPackageName(apkPath);
        SootClass counterClass = createCounterClass(packageName);
        PackManager.v().getPack("jtp").add(new Transform("jtp.test", new ProfilingCodeInjector(counterClass)));
        PackManager.v().getPack("jtp").add(new Transform("jtp.myLogger", new FunctionTracker(counterClass)));
        // PRINT STAGE
        PackManager.v().getPack("jtp").add(new Transform("jtp.print", new BodyTransformer() {
            @Override
            protected void internalTransform(Body b, String phaseName, Map<String, String> options) {
                // First we filter out Android framework methods
                if(AndroidUtil.isAndroidMethod(b.getMethod()))
                    return;
                lock.lock();
                JimpleBody body = (JimpleBody) b;
                System.out.println(body.toString());
                lock.unlock();
            }
        }));
        // Run Soot packs (note that our transformer pack is added to the phase "jtp")
        PackManager.v().runPacks();
        // Write the result of packs in outputPath
        PackManager.v().writeOutput();
    }

    static class ProfilingCodeInjector extends BodyTransformer {

        SootClass counterClass;
        HashMap<String,SootMethod> classToWriteMethods = new HashMap<String, SootMethod>();
        HashMap<String,SootMethod> classToReadMethods = new HashMap<String, SootMethod>();
        public ProfilingCodeInjector(SootClass counterClass) {
            this.counterClass = counterClass;
        }

        @Override
        protected void internalTransform(Body b, String phaseName, Map<String, String> options) {
            // First we filter out Android framework methods
            if(AndroidUtil.isAndroidMethod(b.getMethod()))
                return;
            lock.lock();
            JimpleBody body = (JimpleBody) b;
            instrumentBody(body, this.counterClass, this.classToReadMethods, this.classToWriteMethods);
            lock.unlock();
        }
    }

    static SootClass createCounterClass(String packageName) {
        String signature = packageName + ".StaticCounter";
        SootClass counterClass = new SootClass(signature, Modifier.PUBLIC);
        counterClass.setSuperclass(Scene.v().getSootClass("java.lang.Object")); 
        counterClass.setApplicationClass();
        return counterClass;
    }

    static String findClassName(JInstanceFieldRef fieldRef) {
        return fieldRef.getField()
                       .getDeclaringClass()
                       .getName();
    }

    static void instrumentBody(JimpleBody body, SootClass counterClass, 
                    HashMap<String,SootMethod> classToReadMethods, 
                    HashMap<String,SootMethod> classToWriteMethods) {
        UnitPatchingChain units = body.getUnits();
        Iterator<Unit> it = units.iterator();
        ArrayList<InsertionPair<Unit>> insertionPairs = new ArrayList<InsertionPair<Unit>>();
        while (it.hasNext()) {
            Unit unit = it.next();
            if (unit instanceof JAssignStmt) {
                Value lhs = ((JAssignStmt)unit).getLeftOp();
                Value rhs = ((JAssignStmt)unit).getRightOp();
                if (lhs instanceof JInstanceFieldRef) {
                    String fullClassName = findClassName((JInstanceFieldRef)lhs);
                    generateMethods(fullClassName, counterClass, classToReadMethods, classToWriteMethods);
                    insertionPairs.add(
                        generateInsertionPair(fullClassName, classToReadMethods, unit)
                    );
                }
                if (rhs instanceof JInstanceFieldRef) {
                    String fullClassName = findClassName((JInstanceFieldRef)rhs);
                    generateMethods(fullClassName, counterClass, classToReadMethods, classToWriteMethods);
                    insertionPairs.add(
                        generateInsertionPair(fullClassName, classToReadMethods, unit)
                    );
                }
            }
        }
        for (InsertionPair<Unit> pair : insertionPairs) {
            units.insertBefore(pair.toInsert, pair.point);
        }
        body.validate();
    }

    static void generateMethods(String fullClassName, SootClass counterClass, 
                    HashMap<String,SootMethod> classToReadMethods, 
                    HashMap<String,SootMethod> classToWriteMethods) {
        if (!classToReadMethods.containsKey(fullClassName)) {
            SootMethod incReadMethod = generateReadCounter(fullClassName, counterClass);
            SootMethod incWriteMethod = generateWriteCounter(fullClassName, counterClass);
            classToReadMethods.put(fullClassName, incReadMethod);
            classToWriteMethods.put(fullClassName, incWriteMethod);
        }
    }

    static InsertionPair generateInsertionPair(String fullClassName, HashMap<String, SootMethod> classToMethods, Unit unit) {
        SootMethod method = classToMethods.get(fullClassName);
        Unit call = Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(method.makeRef()));
        InsertionPair<Unit> pair = new InsertionPair<Unit>(call, unit);
        return pair;
    }

    static SootMethod generateReadCounter(String fullClassName, SootClass counterClass) {
        String [] strArray = fullClassName.split("\\.");
        String typeName = strArray[strArray.length - 1];
        String joinedName = String.join("", strArray);
        SootField readCounter = addCounter(joinedName + "Read", counterClass);
        SootMethod readIncMethod = createMethod(counterClass,  
            joinedName + "Read", fullClassName + " read", readCounter);
        return readIncMethod;
    }

    static SootMethod generateWriteCounter(String fullClassName, SootClass counterClass) {
        String [] strArray = fullClassName.split("\\.");
        String typeName = strArray[strArray.length - 1];
        String joinedName = String.join("", strArray);
        SootField writeCounter = addCounter(joinedName + "Write", counterClass);
        SootMethod writeIncMethod = createMethod(counterClass, 
            joinedName + "Write", fullClassName + " write", writeCounter);
        return writeIncMethod;
    }
    static SootMethod generateFunctionCounter(String fullFunctionName, SootClass counterClass) {
        String [] strArray = fullFunctionName.split("\\.");
        String functionName = strArray[strArray.length - 1];
        String joinedName = String.join("", strArray);
        SootField functionCounter = addCounter(joinedName + "Call", counterClass);
        SootMethod functionIncMethod = createMethod(counterClass, 
            joinedName + "Call", fullFunctionName + " function call", functionCounter);
        return functionIncMethod;

    }

    // Create new counter for every new object type encountered
    static SootField addCounter(String name, SootClass counterClass) {
        SootField counterField = new SootField(name + "Counter", 
            IntType.v(), Modifier.PUBLIC | Modifier.STATIC);
        counterClass.addField(counterField);
        return counterField;
    }

    static SootMethod createMethod(SootClass counterClass, String name, String nameForLog, SootField counterField) {
        String methodName = "increment" + name;
        SootMethod incMethod = new SootMethod(methodName,
            Arrays.asList(new Type[]{}),
            VoidType.v(), Modifier.PUBLIC | Modifier.STATIC);
        generatedFunctionNames.add(methodName);
        counterClass.addMethod(incMethod);
        JimpleBody body = Jimple.v().newBody(incMethod);
        UnitPatchingChain units = body.getUnits();
        Local counterLocal = InstrumentUtil.generateNewLocal(body, IntType.v());
        units.add(Jimple.v().newAssignStmt(counterLocal, Jimple.v().newStaticFieldRef(counterField.makeRef())));
 
        units.add(Jimple.v().newAssignStmt(counterLocal, 
                Jimple.v().newAddExpr(counterLocal, IntConstant.v(1))));
        units.add(Jimple.v().newAssignStmt(Jimple.v().newStaticFieldRef(counterField.makeRef()), counterLocal));
        units.addAll(InstrumentUtil.generateLogStmts(body, nameForLog + " counter = ", counterLocal));
        Unit returnUnit = Jimple.v().newReturnVoidStmt();
        units.add(returnUnit);
        body.validate();
        incMethod.setActiveBody(body);
        return incMethod;
    }

    static String findFullMethodName(SootMethod method) {
        String name = method.getName();
        name = name.replace("<", "");
        name = name.replace(">", "");
        return method.getDeclaringClass().getName() + "_" + name;
    }
 
    static class FunctionTracker extends BodyTransformer {

        SootClass counterClass;
        HashSet<String> counterMethodNames = new HashSet<String>();
        HashMap<String,SootMethod> functionNamesToMethods = new HashMap<String, SootMethod>();
        public FunctionTracker(SootClass counterClass) {
            this.counterClass = counterClass;
        }

        @Override
        protected void internalTransform(Body b, String phaseName, Map<String, String> options) {
            // First we filter out Android framework methods
            if(AndroidUtil.isAndroidMethod(b.getMethod()) || generatedFunctionNames.contains(b.getMethod().getName())) {
                return;
            }
            JimpleBody body = (JimpleBody) b;
            UnitPatchingChain units = b.getUnits();
            String fullMethodString = findFullMethodName(b.getMethod());
            if (this.counterMethodNames.contains(fullMethodString)) {
                return;
            }
            this.counterMethodNames.add(fullMethodString);
            SootMethod counterMethod = generateFunctionCounter(fullMethodString, this.counterClass);
 //           List<Unit> generatedUnits = new ArrayList<>();
            // The message that we want to log
//            String content = String.format("%s Beginning of method %s", InstrumentUtil.TAG, body.getMethod().getSignature());
            // In order to call "System.out.println" we need to create a local containing "System.out" value
/*
            Local psLocal = InstrumentUtil.generateNewLocal(body, RefType.v("java.io.PrintStream"));
            // Now we assign "System.out" to psLocal
            SootField sysOutField = Scene.v().getField("<java.lang.System: java.io.PrintStream out>");
            AssignStmt sysOutAssignStmt = Jimple.v().newAssignStmt(psLocal, Jimple.v().newStaticFieldRef(sysOutField.makeRef()));
            generatedUnits.add(sysOutAssignStmt);

            // Create println method call and provide its parameter
            SootMethod printlnMethod = Scene.v().grabMethod("<java.io.PrintStream: void println(java.lang.String)>");
            Value printlnParamter = StringConstant.v(content);
            InvokeStmt printlnMethodCallStmt = Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr(psLocal, printlnMethod.makeRef(), printlnParamter));
            generatedUnits.add(printlnMethodCallStmt);
*/

            Unit call = Jimple.v().newInvokeStmt(Jimple.v().newStaticInvokeExpr(counterMethod.makeRef()));
            // Insert the generated statement before the first  non-identity stmt
            units.insertBefore(call, body.getFirstNonIdentityStmt());
            // Validate the body to ensure that our code injection does not introduce any problem (at least statically)
            b.validate();
        }
    } 
}

class InsertionPair<E> {
    protected final E toInsert;
    protected final E point;
    public InsertionPair(E toInsert, E point) {
        this.toInsert = toInsert;
        this.point = point; 
    }
}

