package dev.navids.soottutorial.android;

import soot.*;
import soot.jimple.*;
import soot.jimple.internal.*;

import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;

public class ArrayWrapperCreator {
    SootClass counterClass;
    String packageName; 
    HashMap <String, SootClass> arrayClasses;
    public ArrayWrapperCreator(SootClass counterClass, String packageName) {
        this.counterClass = counterClass;
        this.packageName = packageName;
        this.arrayClasses = new HashMap<>();
    }

    public SootMethod createArrayConstructor(SootClass arrayClass, String arrayClassName, Type arrayType, SootField counterField) {

        String methodName = "<init>";
        SootMethod constructor = new SootMethod(methodName,
            Arrays.asList(new Type[]{arrayType}),
            VoidType.v(), Modifier.PUBLIC);
        arrayClass.addMethod(constructor);
        JimpleBody body = Jimple.v().newBody(constructor);
        UnitPatchingChain units = body.getUnits();
        Value thisRef = Jimple.v().newThisRef(arrayClass.getType());
        Local thisLocal = InstrumentUtil.generateNewLocal(body, arrayClass.getType());
        units.add(Jimple.v().newIdentityStmt(thisLocal, thisRef));
        Local paramLocal = InstrumentUtil.generateNewLocal(body, arrayType);
        ParameterRef arrayParam = Jimple.v().newParameterRef(arrayType, 0);
        units.add(Jimple.v().newIdentityStmt(paramLocal, arrayParam));
        InstanceFieldRef arrayFieldRef = Jimple.v().newInstanceFieldRef(thisLocal, 
            arrayClass.getFieldByName("array").makeRef());
        units.add(Jimple.v().newAssignStmt(arrayFieldRef, paramLocal));

        Local counterLocal = InstrumentUtil.generateNewLocal(body, IntType.v());
        units.add(Jimple.v().newAssignStmt(counterLocal, Jimple.v().newStaticFieldRef(counterField.makeRef())));
        units.add(Jimple.v().newAssignStmt(counterLocal, 
                Jimple.v().newAddExpr(counterLocal, IntConstant.v(1))));
        units.add(Jimple.v().newAssignStmt(Jimple.v().newStaticFieldRef(counterField.makeRef()), counterLocal));

        units.addAll(InstrumentUtil.generateLogStmts(body, arrayClass.getName() + " intiailized id = ", counterLocal));

        units.add(Jimple.v().newInvokeStmt(Jimple.v().newSpecialInvokeExpr(thisLocal, arrayClass.getSuperclass().getMethodByName("<init>").makeRef())));
        Unit returnUnit = Jimple.v().newReturnVoidStmt();
        units.add(returnUnit);

        System.out.println("NEW CONSTRUCTOR:\n" + body.toString());
        body.validate();
        constructor.setActiveBody(body);
        return constructor;
    }

    public void createArrayGetter(SootClass arrayClass, String arrayClassName, ArrayType arrayType, SootMethod incReads) {
        Type elementType = arrayType.getElementType();
        String methodName = "get";
        SootMethod getter = new SootMethod(methodName,
            Arrays.asList(new Type[]{IntType.v()}),
            elementType, Modifier.PUBLIC);
        arrayClass.addMethod(getter);
        JimpleBody body = Jimple.v().newBody(getter);
        UnitPatchingChain units = body.getUnits();
        Value thisRef = Jimple.v().newThisRef(arrayClass.getType());
        Local thisLocal = InstrumentUtil.generateNewLocal(body, arrayClass.getType());
        units.add(Jimple.v().newIdentityStmt(thisLocal, thisRef));
        Local indexLocal = InstrumentUtil.generateNewLocal(body, IntType.v());
        ParameterRef indexParam = Jimple.v().newParameterRef(IntType.v(), 0);
        units.add(Jimple.v().newIdentityStmt(indexLocal, indexParam));
        Local arrayLocal = InstrumentUtil.generateNewLocal(body, arrayType);
        InstanceFieldRef serialFieldRef = Jimple.v().newInstanceFieldRef(thisLocal, arrayClass.getFieldByName("array").makeRef());
        units.add(Jimple.v().newAssignStmt(arrayLocal, serialFieldRef));
        Local valueLocal = InstrumentUtil.generateNewLocal(body, elementType);
        units.add(Jimple.v().newAssignStmt(valueLocal, Jimple.v().newArrayRef(arrayLocal, indexLocal)));
        Unit call = Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr(thisLocal, incReads.makeRef()));
        units.add(call);
        Unit returnUnit = Jimple.v().newReturnStmt(valueLocal);
        units.add(returnUnit);
        System.out.println("NEW GETTER:\n" + body.toString());
        body.validate();
        getter.setActiveBody(body);
    }
    public void createArraySetter(SootClass arrayClass, String arrayClassName, ArrayType arrayType, SootMethod incWrites) {
        Type elementType = arrayType.getElementType();
        String methodName = "set";
        SootMethod setter = new SootMethod(methodName,
            Arrays.asList(new Type[]{IntType.v(), elementType}),
            VoidType.v(), Modifier.PUBLIC);
        arrayClass.addMethod(setter);
        JimpleBody body = Jimple.v().newBody(setter);
        UnitPatchingChain units = body.getUnits();
        Value thisRef = Jimple.v().newThisRef(arrayClass.getType());
        Local thisLocal = InstrumentUtil.generateNewLocal(body, arrayClass.getType());
        units.add(Jimple.v().newIdentityStmt(thisLocal, thisRef));
        Local indexLocal = InstrumentUtil.generateNewLocal(body, IntType.v());
        ParameterRef indexParam = Jimple.v().newParameterRef(IntType.v(), 0);
        units.add(Jimple.v().newIdentityStmt(indexLocal, indexParam));
        Local valueLocal = InstrumentUtil.generateNewLocal(body, elementType);
        ParameterRef valueParam = Jimple.v().newParameterRef(elementType, 1);
        units.add(Jimple.v().newIdentityStmt(valueLocal, valueParam));
        Local arrayLocal = InstrumentUtil.generateNewLocal(body, arrayType);
        InstanceFieldRef serialFieldRef = Jimple.v().newInstanceFieldRef(thisLocal, 
            arrayClass.getFieldByName("array").makeRef());
        units.add(Jimple.v().newAssignStmt(arrayLocal, serialFieldRef));
        units.add(Jimple.v().newAssignStmt(Jimple.v().newArrayRef(arrayLocal, indexLocal), valueLocal));
        Unit call = Jimple.v().newInvokeStmt(Jimple.v().newVirtualInvokeExpr(thisLocal, incWrites.makeRef()));
        units.add(call);
        Unit returnUnit = Jimple.v().newReturnVoidStmt();
        units.add(returnUnit);
        System.out.println("NEW SETTER:\n" + body.toString());
        body.validate();
        setter.setActiveBody(body);
    }

    public void createArrayAccessMethods(SootClass arrayClass, String arrayClassName, 
                ArrayType arrayType, SootMethod incReads, SootMethod incWrites) {
        createArrayGetter(arrayClass, arrayClassName, arrayType, incReads); 
        createArraySetter(arrayClass, arrayClassName, arrayType, incWrites);  
    }

    public SootClass createArrayClass(JNewArrayExpr arrayExpr) {
        Type arrayType = arrayExpr.getType();
        String arrayClassName = arrayType
            .toString()
            .replace(".", "")
            .replace("[", "")
            .replace("]", "Array");

        if (this.arrayClasses.containsKey(arrayClassName)) {
            return this.arrayClasses.get(arrayClassName);
        }
        String signature = this.packageName + "." + arrayClassName;
        SootClass arrayClass = new SootClass(signature, Modifier.PUBLIC);
        arrayClass.setSuperclass(Scene.v().getSootClass("java.lang.Object")); 
        arrayClass.setApplicationClass();

        HashMap <String, ObjectProfilingData> classNamesToObjectData = new HashMap<>();
        HashMap <String, SootMethod> classNamesToReadIncrementors = new HashMap<>();
        HashMap <String, SootMethod> classNamesToWriteIncrementors = new HashMap<>();
        ClassInstrumentationUtil.addObjectAccessFields(arrayClass, this.counterClass, classNamesToObjectData, 
              classNamesToReadIncrementors, classNamesToWriteIncrementors);
        SootField array = new SootField("array", arrayType);
        arrayClass.addField(array);
        System.out.println("Created class " + signature);
        System.out.println("Array type = " + arrayType.toString() + ", element type = " + ((ArrayType)arrayType).getElementType().toString());
        ObjectProfilingData data = classNamesToObjectData.get(arrayClass.getName());
        SootMethod constructor = createArrayConstructor(arrayClass, arrayClassName, arrayType, data.staticCounter); 

        String [] strArray = arrayClass.getName().split("\\.");
        String className = strArray[strArray.length - 1];
        String joinedClassName = String.join("", strArray);
        SootMethod incReads = classNamesToReadIncrementors.get(joinedClassName);
        SootMethod incWrites = classNamesToWriteIncrementors.get(joinedClassName);
        createArrayAccessMethods(arrayClass, arrayClassName, (ArrayType)arrayType, incReads, incWrites);
        this.arrayClasses.put(arrayClassName, arrayClass);
        return arrayClass; 
    }
}
