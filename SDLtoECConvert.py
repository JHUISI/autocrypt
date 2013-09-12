import copy
import sdlpath
from sdlparser.SDLParser import *
import re, importlib

symmetricPairingSettingKeyword_SDL = "symmetric"
asymmetricPairingSettingKeyword_SDL = "asymmetric"
generatorVarNameToNewName = {}
gameEndChar_EC = "."
memKeyword_EC = "mem"
notOperator_EC = "!"
andOperator_EC = "&&"
#constantGeneratorVarName_EC = "g_1"
initFuncName_EC = "Init"
dummyVarInMain_EC = "dummy"
vVarInMain_EC = "v"
additionOperator_EC = "+"
intType_EC = "int"
countVarPrefix = "count_"
advPubKeyVarName_EC = "adv_public_key"
adversaryVarName_EC = "Adv"
adversaryKeyword_EC = "adversary"
funcNamesAdvDoesntNeed = ["types", "count", "precompute", "NONE_FUNC_NAME"]
sVarInMain_EC = "s"
messageVarNameInMain_EC = "m"
emptyMapSymbol_EC = "[]"
emptyMapName_EC = "empty_map"
randomOracleVarName_EC = "rand_oracle"
randomG1GenerationStmt_EC = "Rand_G_1()"
randomG2GenerationStmt_EC = "Rand_G_2()"
randomZRGenerationStmt_EC = "Rand_exp()"
funcName_EC = "fun"
trueKeyword_EC = "true"
trueKeyword_SDL = "True"
falseKeyword_EC = "false"
falseKeyword_SDL = "False"
numSpacesForIndent = 2
templateFileName = "ECTemplate_SymmOrAsymm"
templateFileExt = ".txt"
#configFileName = "SDLtoECConfig"
booleanType_EC = "bool"
varKeyword_EC = "var"
abstractKeyword_EC = "abs"
adversaryIdentifier_EC = "A"
adversarySignatureIdentifier_EC = "Adv"
hashFuncName_EC = "Hash"
signFuncName_EC = "Sign"
verifyFuncName_EC = "Verify"
messageName_EC = "m"
messageType_EC = "message"
secretKeyName_EC = "secret_key"
queriedName_EC = "queried"
varNameForVerifyBoolRetVal_EC = "v"
appendOperator_EC = "::"
funcStartChar_EC = "{"
funcEndChar_EC = "}"
assignmentOperator_EC = "="
returnKeyword_EC = "return"
multOp_EC = "*"
expOp_EC = "^"
endOfLineOperator_EC = ";"
eqTstOperator_EC = "="
validGroupTypes = ["G1", "G2", "GT", "ZR"]
validHashGroupTypes = ["G1", "G2", "ZR"]
validRandomGroupTypes = ["G1", "G2", "ZR"]

DEBUG = False

def writeNumOfSpacesToString(numSpaces):
    outputString = ""

    for space in range(0, numSpaces):
        outputString += " "

    return outputString

def addTemplateLinesFromOneTemplateFileToOutputECFile(outputECFile, generatorCounter):
    templateFile = open(templateFileName + str(generatorCounter) + templateFileExt, 'r')
    outputString = ""

    for templateLine in templateFile:
        outputString += templateLine

    outputECFile.write(outputString)

def addTemplateLinesToOutputECFile_SymmetricOrAsymmetric(outputECFile, assignInfo, generatorsList, pairingSetting, config):
    global generatorVarNameToNewName

    #generatorVarNameToNewName["g"] = "g_1"
    #generatorVarNameToNewName["var2"] = "g_2"

    #addTemplateLinesFromOneTemplateFileToOutputECFile(outputECFile, 1)

    outputString = ""
    outputString += "prover alt-ergo, z3, cvc3.\n\n"

    if (pairingSetting == symmetricPairingSettingKeyword_SDL):
        outputString += "type G_1.\n"
    else:
        outputString += "type G_1.\n"
        outputString += "type G_2.\n"

    #outputECFile.write(outputString)

    outputString += "type G_T.\n"
    outputString += "type message.\n\n"
    outputString += "cnst g_1_i : G_1.\n"

    #addTemplateLinesFromOneTemplateFileToOutputECFile(outputECFile, 2)

    #outputString = ""

    if (pairingSetting == asymmetricPairingSettingKeyword_SDL):
        outputString += "cnst g_2_i : G_2.\n"

    outputString += "cnst g_T_i : G_T.\n"

    generatorCounter = 1

    for generator in generatorsList:
        #print(generator)
        outputString += "cnst g_" + str(generatorCounter) + " : " 
        typeForThisGenerator = getVarTypeFromVarName_EC(generator, config.keygenFuncName_SDL, pairingSetting)
        outputString += typeForThisGenerator + ".\n"
        generatorVarNameToNewName[generator] = "g_" + str(generatorCounter)
        generatorCounter += 1

    outputString += "cnst g_T : G_T.\n"
    outputString += "cnst q_1 : int.\n"

    if (pairingSetting == asymmetricPairingSettingKeyword_SDL):
        outputString += "cnst q_2 : int.\n"

    outputString += "cnst q_T : int.\n\n"

    outputString += "cnst q : int.\n\n"

    outputString += "cnst limit_Hash : int.\n\n"
    outputString += "op [*] : (G_1, G_1) -> G_1 as G_1_mul.\n"

    if (pairingSetting == asymmetricPairingSettingKeyword_SDL):
        outputString += "op [*] : (G_2, G_2) -> G_2 as G_2_mul.\n"

    if (pairingSetting == symmetricPairingSettingKeyword_SDL):
        outputString += "op [^] : (G_1, int) -> G_1 as G_1_pow.\n\n"
    else:
        outputString += "op [^] : (G_1, int) -> G_1 as G_1_pow.\n"
        outputString += "op [^] : (G_2, int) -> G_2 as G_2_pow.\n\n"

    outputString += "op [*] : (G_T, G_T) -> G_T as G_T_mul.\n"
    outputString += "op [^] : (G_T, int) -> G_T as G_T_pow.\n\n"
    outputString += "op G_1_log : G_1 -> int.\n"

    if (pairingSetting == asymmetricPairingSettingKeyword_SDL):
        outputString += "op G_2_log : G_2 -> int.\n"

    outputString += "op G_T_log : G_T -> int.\n\n"

    if (pairingSetting == symmetricPairingSettingKeyword_SDL):
        outputString += "op e : (G_1, G_1) -> G_T as G_1_pair.\n\n"
    else:
        outputString += "op e : (G_1, G_2) -> G_T as G_1_G_2_pair.\n\n"

    outputString += "(*\n"
    outputString += "   From easycrypt ElGamal:\n"
    outputString += "   If we use the native modulo alt-ergo is not able\n"
    outputString += "   to perform the proof.\n"
    outputString += "   So we declare an operator (%%) which stand for the modulo ...\n"
    outputString += "*)\n\n"
    outputString += "op [%%] : (int,int) -> int as int_mod.\n\n"

    if (pairingSetting == symmetricPairingSettingKeyword_SDL):
        outputString += "axiom q_1_pos : 0 < q_1.\n"
    else:
        outputString += "axiom q_1_pos : 0 < q_1.\n"
        outputString += "axiom q_2_pos : 0 < q_2.\n"

    outputString += "axiom q_T_pos : 0 < q_T.\n\n"

    outputString += "axiom q_pos : 0 < q.\n\n"

    if (pairingSetting == symmetricPairingSettingKeyword_SDL):
        outputString += "(* Axioms largely pulled from ElGamal.  Note that G_1 and G_T have the same order if the order is prime. *)\n\n"
    else:
        outputString += "(* Axioms largely pulled from ElGamal.  Note that G_1, G_2, and G_T have the same order if the order is prime. *)\n\n"

    outputString += "axiom G_1_mult_1 : forall (x : G_1), x * g_1_i = x.\n"
    outputString += "axiom G_1_exp_0 : forall (x : G_1), x ^ 0 = g_1_i.\n"
    outputString += "axiom G_1_exp_S : forall (x : G_1, k : int), k > 0 => x ^ k = x * (x^(k-1)).\n\n"

    if (pairingSetting == asymmetricPairingSettingKeyword_SDL):
        outputString += "axiom G_2_mult_1 : forall (x : G_2), x * g_2_i = x.\n"
        outputString += "axiom G_2_exp_0 : forall (x : G_2), x ^ 0 = g_2_i.\n"
        outputString += "axiom G_2_exp_S : forall (x : G_2, k : int), k > 0 => x ^ k = x * (x^(k-1)).\n\n"

    outputString += "axiom G_T_mult_1 : forall (x : G_T), x * g_T_i = x.\n"
    outputString += "axiom G_T_exp_0 : forall (x : G_T), x ^ 0 = g_T_i.\n"
    outputString += "axiom G_T_exp_S : forall (x : G_T, k : int), k > 0 => x ^ k = x * (x^(k-1)).\n\n"

    if (pairingSetting == symmetricPairingSettingKeyword_SDL):
        outputString += "axiom bilinearity : forall (x : G_1, y : G_1, a : int, b : int), e(x ^ a, y ^ b) = e(x, y) ^ (a * b).\n"
        outputString += "(* axiom non_degenerate : !(e(g_1, g_1) = g_T_i). *)\n\n"
    else:
        outputString += "axiom bilinearity : forall (x : G_1, y : G_2, a : int, b : int), e(x ^ a, y ^ b) = e(x, y) ^ (a * b).\n"
        outputString += "(* axiom non_degenerate : !(e(g_1, g_2) = g_T_i). *)\n\n"

    generatorCounter = 1

    for generator in generatorsList:
        outputString += "axiom "
        typeForThisGenerator = getVarTypeFromVarName_EC(generator, config.keygenFuncName_SDL, pairingSetting)
        outputString += typeForThisGenerator + "_pow_add_" + str(generatorCounter) + " :\n"
        outputString += " forall (x, y:int), g_" + str(generatorCounter) + " ^ (x + y) = g_"
        outputString += str(generatorCounter) + " ^ x * g_" + str(generatorCounter) + " ^ y.\n\n"
        generatorCounter += 1

    outputString += "axiom G_T_pow_add :\n"
    outputString += " forall (x, y:int), g_T ^ (x + y) = g_T ^ x * g_T ^ y.\n\n"

    generatorCounter = 1

    for generator in generatorsList:
        outputString += "axiom "
        typeForThisGenerator = getVarTypeFromVarName_EC(generator, config.keygenFuncName_SDL, pairingSetting)
        outputString += typeForThisGenerator + "_pow_mult_" + str(generatorCounter) + " :\n"
        outputString += " forall (x, y:int),  (g_" + str(generatorCounter) + " ^ x) ^ y = g_"
        outputString += str(generatorCounter) + " ^ (x * y).\n\n"
        generatorCounter += 1

    outputString += "axiom G_T_pow_mult :\n"
    outputString += " forall (x, y:int),  (g_T ^ x) ^ y = g_T ^ (x * y).\n\n"

    generatorCounter = 1

    for generator in generatorsList:
        outputString += "axiom " 
        typeForThisGenerator = getVarTypeFromVarName_EC(generator, config.keygenFuncName_SDL, pairingSetting)
        outputString += typeForThisGenerator + "_log_pow_" + str(generatorCounter) + " :\n"
        outputString += " forall (g_" + str(generatorCounter) + "': " + typeForThisGenerator + "), g_"
        outputString += str(generatorCounter) + " ^ " + typeForThisGenerator + "_log(g_"
        outputString += str(generatorCounter) + "') = g_" + str(generatorCounter) + "'.\n\n"
        generatorCounter += 1

    outputString += "axiom G_T_log_pow :\n"
    outputString += " forall (g_T':G_T), g_T ^ G_T_log(g_T') = g_T'.\n\n"

    generatorCounter = 1

    for generator in generatorsList:
        outputString += "axiom " 
        typeForThisGenerator = getVarTypeFromVarName_EC(generator, config.keygenFuncName_SDL, pairingSetting)
        outputString += typeForThisGenerator + "_pow_mod_" + str(generatorCounter) + " :\n"
        if (typeForThisGenerator == "G_1"):
            outputString += " forall (z:int), g_" + str(generatorCounter) + " ^ (z%%q_1) = g_"
            outputString += str(generatorCounter) + " ^ z.\n\n"
        elif (typeForThisGenerator == "G_2"):
            outputString += " forall (z:int), g_" + str(generatorCounter) + " ^ (z%%q_2) = g_"
            outputString += str(generatorCounter) + " ^ z.\n\n"
        else:
            sys.exit("addTemplateLinesToOutputECFile_SymmetricOrAsymmetric in SDLtoECConvert.py:  one of the generators is not of type G1 or G2.")
        generatorCounter += 1

    outputString += "axiom G_T_pow_mod :\n"
    outputString += " forall (z:int), g_T ^ (z%%q_T) = g_T ^ z.\n\n"

    outputString += "axiom mod_add :\n"
    outputString += " forall (x,y:int), (x%%q + y)%%q = (x + y)%%q.\n\n"
    outputString += "axiom mod_small :\n"
    outputString += " forall (x:int), 0 <= x => x < q => x%%q = x.\n\n"
    outputString += "axiom mod_sub :\n"
    outputString += " forall (x, y:int), (x%%q - y)%%q = (x - y)%%q.\n\n"
    outputString += "axiom mod_bound :\n"
    outputString += " forall (x:int), 0 <= x%%q && x%%q < q.\n\n"

    outputString += "pop Rand_exp : () -> (int).\n"
    outputString += "pop Rand_G_1 : () -> (G_1).\n"

    if (pairingSetting == asymmetricPairingSettingKeyword_SDL):
        outputString += "pop Rand_G_2 : () -> (G_2).\n"

    outputString += "\n"

    outputString += "(* axiom Rand_G_1_exp_def() : x = Rand_G_1_exp() ~ y = [0..q-1] : true ==> x = y. *)\n"

    outputString += "axiom Rand_G_1_def() : x = Rand_G_1() ~ y = Rand_exp() : true ==> x = g_"

    # this is questionable.  Not sure how best to do this.  Basically, we're just finding the first
    # generator in the group we want, but I don't know if that is technically correct.

    generatorCounter = 1
    foundIt = False

    for generator in generatorsList:
        typeForThisGenerator = getVarTypeFromVarName_EC(generator, config.keygenFuncName_SDL, pairingSetting)
        if (typeForThisGenerator == "G_1"):
            foundIt = True
            break
        generatorCounter += 1

    if (foundIt == False):
        sys.exit("addTemplateLinesToOutputECFile_SymmetricOrAsymmetric in SDLtoECConvert.py:  could not locate a generator of type G1.")

    outputString += str(generatorCounter) + " ^ y.\n\n"

    if (pairingSetting == asymmetricPairingSettingKeyword_SDL):
        outputString += "axiom Rand_G_2_def() : x = Rand_G_2() ~ y = Rand_exp() : true ==> x = g_"

        # again, this is questionable.  Not sure how best to do this.  Basically, we're just finding the first
        # generator in the group we want, but I don't know if that is technically correct.

        generatorCounter = 1
        foundIt = False

        for generator in generatorsList:
            typeForThisGenerator = getVarTypeFromVarName_EC(generator, config.keygenFuncName_SDL, pairingSetting)
            if (typeForThisGenerator == "G_2"):
                foundIt = True
                break
            generatorCounter += 1

        if (foundIt == False):
            sys.exit("addTemplateLinesToOutputECFile_SymmetricOrAsymmetric in SDLtoECConvert.py:  could not locate a generator of type G2, even though the pairing setting is asymmetric.")

        outputString += str(generatorCounter) + " ^ y.\n\n"

    outputECFile.write(outputString)

    #ENDSHERE

# the following function is defunct and is not used.  Ignore it.
def addTemplateLinesToOutputECFile(outputECFile, assignInfo, generatorsList, pairingSetting):
    global generatorVarNameToNewName

    addTemplateLinesFromOneTemplateFileToOutputECFile(outputECFile, 1)

    outputString = ""
    generatorCounter = 1

    for generator in generatorsList:
        outputString += "cnst g_" + str(generatorCounter) + " : G_1.\n"
        generatorVarNameToNewName[generator] = "g_" + str(generatorCounter)
        generatorCounter += 1

    outputECFile.write(outputString)

    addTemplateLinesFromOneTemplateFileToOutputECFile(outputECFile, 2)

    outputString = ""
    generatorCounter = 1

    for generator in generatorsList:
        outputString += "axiom G_1_pow_add_" + str(generatorCounter) + " :\n"
        outputString += " forall (x, y:int), g_" + str(generatorCounter) + " ^ (x + y) = g_"
        outputString += str(generatorCounter) + " ^ x * g_" + str(generatorCounter) + " ^ y.\n\n"
        generatorCounter += 1

    outputECFile.write(outputString)

    addTemplateLinesFromOneTemplateFileToOutputECFile(outputECFile, 3)

    outputString = ""
    generatorCounter = 1

    for generator in generatorsList:
        outputString += "axiom G_1_pow_mult_" + str(generatorCounter) + " :\n"
        outputString += " forall (x, y:int),  (g_" + str(generatorCounter) + " ^ x) ^ y = g_"
        outputString += str(generatorCounter) + " ^ (x * y).\n\n"
        generatorCounter += 1

    outputECFile.write(outputString)

    addTemplateLinesFromOneTemplateFileToOutputECFile(outputECFile, 4)

    outputString = ""
    generatorCounter = 1

    for generator in generatorsList:
        outputString += "axiom G_1_log_pow_" + str(generatorCounter) + " :\n"
        outputString += " forall (g_" + str(generatorCounter) + "':G_1), g_" + str(generatorCounter)
        outputString += " ^ G_1_log(g_" + str(generatorCounter) + "') = g_" + str(generatorCounter)
        outputString += "'.\n\n"
        generatorCounter += 1

    outputECFile.write(outputString)

    addTemplateLinesFromOneTemplateFileToOutputECFile(outputECFile, 5)

    outputString = ""
    generatorCounter = 1

    for generator in generatorsList:
        outputString += "axiom G_1_pow_mod_" + str(generatorCounter) + " :\n"
        outputString += " forall (z:int), g_" + str(generatorCounter) + " ^ (z%%q) = g_"
        outputString += str(generatorCounter) + " ^ z.\n\n"
        generatorCounter += 1

    outputECFile.write(outputString)

    addTemplateLinesFromOneTemplateFileToOutputECFile(outputECFile, 6)

    outputString = ""
    generatorCounter = 1

    for generator in generatorsList:
        outputString += "axiom Rand_G_1_def_" + str(generatorCounter)
        outputString += "() : x = Rand_G_1() ~ y = Rand_G_1_exp() : " + trueKeyword_EC + " ==> x = g_"
        outputString += str(generatorCounter) + " ^ y.\n\n"
        generatorCounter += 1

    outputECFile.write(outputString)

def removeChars(inputString, inputChars):
    inputStringSplit = inputString.split(inputChars)
    outputString = ""
    for inputStringSplitInd in inputStringSplit:
        outputString += inputStringSplitInd

    return outputString

def getSchemeName(SDLFileName):
    SDLFileNameSplit = SDLFileName.split("/")
    lenSplit = len(SDLFileNameSplit)
    SDLFileName = SDLFileNameSplit[(lenSplit - 1)]

    SDLFileName = SDLFileName.split(".")[0]
    SDLFileName = removeChars(SDLFileName, "-")
    return SDLFileName

def addGameDeclLine(SDLFileName, outputECFile):
    schemeName = getSchemeName(SDLFileName)

    outputString = "game "
    outputString += schemeName
    outputString += "_EF " + assignmentOperator_EC + " " + funcStartChar_EC + "\n"

    outputECFile.write(outputString)

def getAtLeastOneHashCallOrNot(inputSDLFile):
    atLeastOneHashCall = False

    for inputSDLLine in inputSDLFile:
        inputSDLLine = inputSDLLine.lstrip().rstrip()
        if (inputSDLLine.startswith("#") == True):
            continue

        splitLine = inputSDLLine.split(":=")

        # if it's not an assignment node, then there won't be any hash calls
        if (len(splitLine) == 1):
            continue

        if (len(splitLine) > 2):
            sys.exit("getAtLeastOneHashCallOrNot in SDLtoECConvert.py:  line in input SDL file contains more than one := symbols; not allowed in SDL.")

        rightSide = splitLine[1]
        rightSide = rightSide.lstrip().rstrip()
        if (rightSide.startswith("H(") == True):
            return True

        reResult = re.search('[^a-zA-Z0-9_]H\(', rightSide)
        if (reResult != None):
            return True

    return False

def getVarDeps(assignInfo, config, varName, funcName):
    # NOTE:  this function gets variable dependencies in a very specific way.  If the variable name passed
    # in is comprised of a list, all of the members of that list are returned.  Otherwise, the variable
    # name passed in is returned.  Example:
    #
    # pk := list{g, x}
    # would return [g, x]
    #
    # sk := x ^ y
    # would return sk

    #NOTE:  I AM CONSIDERING CHANGING THIS!!!!!!!!!  DON'T PAY ATTENTION TO WHAT I WROTE ABOVE.

    if (funcName not in assignInfo):
        sys.exit("getVarDeps in SDLtoECConvert.py:  function name passed in isn't in assignInfo.")

    if (varName not in assignInfo[funcName]):
        sys.exit("getVarDeps in SDLtoECConvert.py:  variable name passed in isn't in the entry of assignInfo for the function name passed in.")

    #varDeps = assignInfo[funcName][varName].getListNodesList()
    #if (len(varDeps) == 0):
        #return [varName]

    #return varDeps

    return assignInfo[funcName][varName].getVarDeps()

def addGlobalVars(outputECFile, assignInfo, config, generatorsList, pairingSetting):
    #outputString = "  " + varKeyword_EC + " " + secretKeyName_EC + " : int\n"

    outputString = ""

    secretKeyVars = getVarDeps(assignInfo, config, config.secretKeyName_SDL, config.keygenFuncName_SDL)

    for secretKeyVar in secretKeyVars:
        # generators are generators, so they don't get declared
        if (secretKeyVar in generatorsList):
            continue
        currentVarType = getVarTypeFromVarName_EC(secretKeyVar, config.keygenFuncName_SDL, pairingSetting)
        outputString += "  " + varKeyword_EC + " " + secretKeyVar + " : " + currentVarType + "\n"

    publicKeyVars = getVarDeps(assignInfo, config, config.publicKeyName_SDL, config.keygenFuncName_SDL)

    for publicKeyVar in publicKeyVars:
        # generators are generators, so they don't get declared
        if (publicKeyVar in generatorsList):
            continue
        currentVarType = getVarTypeFromVarName_EC(publicKeyVar, config.keygenFuncName_SDL, pairingSetting)
        outputString += "  " + varKeyword_EC + " " + publicKeyVar + " : " + currentVarType + "\n"

    outputString += "  " + varKeyword_EC + " " + queriedName_EC + " : message list\n"
    outputECFile.write(outputString)

def addGlobalVarsForHashes(outputECFile):
    outputString = "  " + varKeyword_EC + " " + randomOracleVarName_EC + " : (" + messageType_EC
    outputString += ", " + "G_1) map\n"
    outputECFile.write(outputString)

def addHashFuncDef(outputECFile, assignInfo, config, pairingSetting):
    hashGroupTypeOfSigFunc_SDL = getHashGroupTypeOfFunc(config.signFuncName_SDL, assignInfo, config)
    hashGroupTypeOfSigFunc_EC = convertTypeSDLtoEC_Strings(hashGroupTypeOfSigFunc_SDL, pairingSetting)

    outputString = "\n  " + funcName_EC + " " + hashFuncName_EC + "(m : message) : "
    outputString += hashGroupTypeOfSigFunc_EC + " = {\n"
    outputECFile.write(outputString)
    writeCountVarIncrement(outputECFile, hashFuncName_EC)
    outputString = ""
    outputString += "    if(!in_dom(m, " + randomOracleVarName_EC + ")) {\n"
    outputString += "      " + randomOracleVarName_EC + "[m] = Rand_G_1();\n"
    outputString += "    }\n"
    outputString += "    return " + randomOracleVarName_EC + "[m];\n"
    outputString += "  }\n\n"

    outputECFile.write(outputString)

def addStatementsForPresenceOfHashes(outputECFile, assignInfo, config, pairingSetting):
    addGlobalVarsForHashes(outputECFile)
    addHashFuncDef(outputECFile, assignInfo, config, pairingSetting)

def getInputSDLFileMetadata(inputSDLFileName):
    parseFile(inputSDLFileName, False, True)
    assignInfo = getAssignInfo()
    astNodes = getAstNodes()
    return (assignInfo, astNodes)

'''
def getHashGroupTypesRecursive(currentAssignNode, retList):
    if (currentAssignNode == None):
        return

    if (currentAssignNode.type == ops.HASH):
        currentHashGroupType = str(currentAssignNode.right)
        if (len(retList) == 0):
            retList.append(currentHashGroupType)
        else:
            if (currentHashGroupType != retList[0]):
                sys.exit("getHashGroupTypesRecursive in SDLtoECConvert.py:  found hash calls that hash to different group types.  Not currently supported.")

    if (currentAssignNode.left != None):
        getHashGroupTypesRecursive(currentAssignNode.left, retList)
    if (currentAssignNode.right != None):
        getHashGroupTypesRecursive(currentAssignNode.right, retList)

def getHashGroupTypes(currentAssignNode):
    retList = []

    getHashGroupTypesRecursive(currentAssignNode, retList)

    return retList

def getAtLeastOneHashCallOrNot_WithSDLParser(assignInfo):
    for funcName in assignInfo:
        for varName in assignInfo[funcName]:
            varInfoObj = assignInfo[funcName][varName]
            currentAssignNode = varInfoObj.getAssignNode()
            hashGroupTypes = getHashGroupTypes(currentAssignNode)
'''

def getAtLeastOneHashCallOrNot_WithSDLParser(assignInfo):
    for funcName in assignInfo:
        for varName in assignInfo[funcName]:
            varInfoObj = assignInfo[funcName][varName]
            if (len(varInfoObj.getHashArgsInAssignNode()) > 0):
                return True

    return False

def getVarTypeFromVarName_EC(varName, funcName, pairingSetting):
    if DEBUG : print("getVarTypeFromVarName_EC:  varName and funcName are ", varName, " and ", funcName)

    varType_SDL = getVarTypeFromVarName(varName, funcName, False, False)
    if (varType_SDL == types.NO_TYPE):
        sys.exit("getVarTypeFromVarName_EC in SDLtoECConvert.py:  getVarTypeFromVarName returned types.NO_TYPE for variable name " + str(varName) + " and function name " + str(funcName) + ".")

    varType_EC = convertTypeSDLtoEC(varType_SDL, pairingSetting)
    return varType_EC

def writeVarDecls(outputECFile, oldFuncName, assignInfo, config, generatorsList, varsToNotDeclareInputParam, pairingSetting):
    #if DEBUG : print("writeVarDecls:  funcName is ", oldFuncName, " and varsToNotDeclare:  ", varsToNotDeclareInputParam)

    if (oldFuncName not in assignInfo):
        sys.exit("writeVarDecls in SDLtoECConvert.py:  oldFuncName not in assignInfo.")

    outputString = ""

    # public key variables and secret key variables are all declared globally, so don't declare them
    # locally.

    publicKeyVars = getVarDeps(assignInfo, config, config.publicKeyName_SDL, config.keygenFuncName_SDL)
    secretKeyVars = getVarDeps(assignInfo, config, config.secretKeyName_SDL, config.keygenFuncName_SDL)

    listOfVarsToNotDeclare = []

    for publicKeyVar in publicKeyVars:
        if (publicKeyVar not in listOfVarsToNotDeclare):
            listOfVarsToNotDeclare.append(publicKeyVar)

    for secretKeyVar in secretKeyVars:
        if (secretKeyVar not in listOfVarsToNotDeclare):
            listOfVarsToNotDeclare.append(secretKeyVar)

    for varToNotDeclareInputParam in varsToNotDeclareInputParam:
        if (varToNotDeclareInputParam not in listOfVarsToNotDeclare):
            listOfVarsToNotDeclare.append(varToNotDeclareInputParam)

    #if (outputKeyword not in listOfVarsToNotDeclare):
        #listOfVarsToNotDeclare.append(outputKeyword)

    if (config.publicKeyName_SDL not in listOfVarsToNotDeclare):
        listOfVarsToNotDeclare.append(config.publicKeyName_SDL)

    if (config.secretKeyName_SDL not in listOfVarsToNotDeclare):
        listOfVarsToNotDeclare.append(config.secretKeyName_SDL)

    if DEBUG : print("writeVarDecls:  funcName is ", oldFuncName, " and varsToNotDeclare:  ", listOfVarsToNotDeclare)

    for varName in assignInfo[oldFuncName]:
        if (varName == inputKeyword):
            continue

        if (varName in listOfVarsToNotDeclare):
            continue

        # generators don't need to be declared
        if (varName in generatorsList):
            continue

        #for some reason, SDLParser says variables of type "bool" are actually of type "int".
        #Here's a workaround to fix that
        assignNodeRight = str(assignInfo[oldFuncName][varName].getAssignNode().right)
        if ( (assignNodeRight == trueKeyword_SDL) or (assignNodeRight == falseKeyword_SDL) ):
            outputString += "    " + varKeyword_EC + " " + varName + " : " + booleanType_EC + ";\n"
            continue

        varType_EC = getVarTypeFromVarName_EC(varName, oldFuncName, pairingSetting)

        outputString += "    " + varKeyword_EC + " " + varName + " : " + varType_EC + ";\n"

    if (len(outputString) > 0):
        outputECFile.write(outputString)

def writeBodyOfFunc(outputECFile, oldFuncName, astNodes, config, assignStmtsToNotInclude, generatorsList):
    startLineNoOfFunc = getStartLineNoOfFunc(oldFuncName)
    endLineNoOfFunc = getEndLineNoOfFunc(oldFuncName)

    startLineNoOfBody = startLineNoOfFunc + 2
    endLineNoOfBody = endLineNoOfFunc - 1

    writeAstNodesToFile(outputECFile, astNodes, startLineNoOfBody, endLineNoOfBody, config, assignStmtsToNotInclude, generatorsList)

def isAssignStmt(astNode):
    if (astNode.type == ops.EQ):
        return True

    return False

def makeSDLtoECVarNameReplacements(attrAsString, config):
    if (attrAsString == config.messageName_SDL):
        return messageName_EC
    if (attrAsString == config.secretKeyName_SDL):
        return secretKeyName_EC
    return attrAsString

def getAssignStmtAsString(astNode, config, generatorsList):
    if (astNode.type == ops.ATTR):
        attrAsString = str(astNode)
        #attrAsString = makeSDLtoECVarNameReplacements(attrAsString, config)
        if (attrAsString in generatorsList):
            return generatorVarNameToNewName[attrAsString]
            #if (len(generatorsList) == 1):
                # if there's only one generator, that's our generator.  Make the replacement so that our
                # variable name is replaced by the one EC generator generator.
                #return constantGeneratorVarName_EC
            #return constantGeneratorVarName_EC
            #sys.exit("getAssignStmtAsString in SDLtoECConvert.py:  there are multiple constants in the SDL input file.  We don't currently handle that right now.")
        if (attrAsString == trueKeyword_SDL):
            return trueKeyword_EC
        if (attrAsString == falseKeyword_SDL):
            return falseKeyword_EC
        #print(attrAsString)
        #if (attrAsString == NONE_STRING):
            #return ""
        return attrAsString
    elif (astNode.type == ops.TYPE):
        groupTypeAsString = str(astNode)
        if (groupTypeAsString not in validGroupTypes):
            sys.exit("getAssignStmtAsString in SDLtoECConvert.py:  received node of type ops.TYPE, but it is not a valid type.")
        return groupTypeAsString
    elif (astNode.type == ops.EXP):
        leftSide = getAssignStmtAsString(astNode.left, config, generatorsList)
        rightSide = getAssignStmtAsString(astNode.right, config, generatorsList)
        return "(" + leftSide + " " + expOp_EC + " " + rightSide + ")"
    elif (astNode.type == ops.PAIR):
        leftSide = getAssignStmtAsString(astNode.left, config, generatorsList)
        rightSide = getAssignStmtAsString(astNode.right, config, generatorsList)
        return "e(" + leftSide + ", " + rightSide + ")"
    elif (astNode.type == ops.EQ):
        leftSide = getAssignStmtAsString(astNode.left, config, generatorsList)
        rightSide = getAssignStmtAsString(astNode.right, config, generatorsList)
        return leftSide + " " + assignmentOperator_EC + " " + rightSide
    elif (astNode.type == ops.EQ_TST):
        leftSide = getAssignStmtAsString(astNode.left, config, generatorsList)
        rightSide = getAssignStmtAsString(astNode.right, config, generatorsList)
        return "(" + leftSide + " " + eqTstOperator_EC + " " + rightSide + ")"
    elif (astNode.type == ops.HASH):
        leftSide = getAssignStmtAsString(astNode.left, config, generatorsList)
        rightSide = getAssignStmtAsString(astNode.right, config, generatorsList)
        if (rightSide not in validHashGroupTypes):
            sys.exit("getAssignStmtAsString in SDLtoECConvert.py:  received invalid type for hash call.")
        #return hashFuncName_EC + "(" + leftSide + ", " + rightSide + ")"
        return hashFuncName_EC + "(" + leftSide + ")"
    elif (astNode.type == ops.RANDOM):
        randomGroupType = getAssignStmtAsString(astNode.left, config, generatorsList)
        if (randomGroupType not in validRandomGroupTypes):
            sys.exit("getAssignStmtAsString in SDLtoECConvert.py:  received invalid type for random call.")
        if (randomGroupType == str(types.G1)):
            return randomG1GenerationStmt_EC
        elif (randomGroupType == str(types.G2)):
            return randomG2GenerationStmt_EC
        elif (randomGroupType == str(types.ZR)):
            return randomZRGenerationStmt_EC
        else:
            sys.exit("getAssignStmtAsString in SDLtoECConvert.py:  error in system logic for random calls.")
    elif (astNode.type == ops.FUNC):
        funcReturnString = ""
        userFuncName = getFullVarName(astNode, True)
        funcReturnString += userFuncName + "("
        funcListNodes = getListNodeNames(astNode)
        atLeastOneFuncListNode = False
        for funcListNode in funcListNodes:
            if (funcListNode == NONE_STRING):
                continue
            funcReturnString += funcListNode + ", "
            atLeastOneFuncListNode = True
        if (atLeastOneFuncListNode == True):
            lenFuncReturnString = len(funcReturnString)
            funcReturnString = funcReturnString[0:(lenFuncReturnString - len(", "))]
        funcReturnString += ")"
        return funcReturnString
    else:
        sys.exit("getAssignStmtAsString in SDLtoECConvert.py:  could not handle this type (" + str(astNode.type) + ") of node (" + str(astNode) + ").  Need to add more logic to support it.")

def isUnnecessaryNode(astNode):
    if ( (astNode.type == ops.BEGIN) and (astNode.left.attr == IF_BRANCH_HEADER) ):
        return True

    return False

def isIfStmtStart(astNode):
    if (astNode.type == ops.IF):
        return True

    return False

def getIfStmtDecl(astNode, config, generatorsList):
    outputString = ""

    outputString += "if("
    outputString += getAssignStmtAsString(astNode.left, config, generatorsList)
    outputString += ") {"

    return outputString

def getIfStmtEnd(astNode):
    return "}"

def isIfStmtEnd(astNode):
    if ( (astNode.type == ops.END) and (astNode.left.attr == IF_BRANCH_HEADER) ):
        return True

    return False

def isElseStmtStart(astNode):
    if (astNode.type == ops.ELSE):
        return True

    return False

def isNONENode(astNode):
    if (astNode.type == ops.NONE):
        return True

    return False

def getElseStmtStart(astNode, config):
    outputString = ""

    if (astNode.left == None):
        outputString += "else {"
    else:
        outputString += "else if ("
        outputString += getAssignStmtAsString(astNode.left, config, generatorsList)
        outputString += ") {"

    return outputString

def isAssignStmtToNotInclude(astNode, config, assignStmtsToNotInclude, generatorsList):
    if (isAssignStmt(astNode) == False):
        return False

    varNameToBeAssigned = getAssignStmtAsString(astNode.left, config, generatorsList)

    if (varNameToBeAssigned in assignStmtsToNotInclude):
        return True

    if (astNode.right.type == ops.EXPAND):
        return True

    if (astNode.right.type == ops.LIST):
        return True

    return False

def writeAstNodesToFile(outputECFile, astNodes, startLineNo, endLineNo, config, assignStmtsToNotInclude, generatorsList):
    outputString = ""
    currentNumSpaces = (numSpacesForIndent * 2)

    for lineNo in range(startLineNo, (endLineNo + 1)):
        currentAstNode = astNodes[(lineNo - 1)]
        if (isAssignStmtToNotInclude(currentAstNode, config, assignStmtsToNotInclude, generatorsList) == True):
            continue
        elif (isAssignStmt(currentAstNode) == True):
            # generators don't get assignment statements
            if (str(currentAstNode.left) in generatorsList):
                continue
            outputString += writeNumOfSpacesToString(currentNumSpaces)
            outputString += getAssignStmtAsString(currentAstNode, config, generatorsList)
            outputString += endOfLineOperator_EC
        elif (isIfStmtStart(currentAstNode) == True):
            outputString += writeNumOfSpacesToString(currentNumSpaces)
            outputString += getIfStmtDecl(currentAstNode, config, generatorsList)
            currentNumSpaces += numSpacesForIndent
        elif (isIfStmtEnd(currentAstNode) == True):
            currentNumSpaces -= numSpacesForIndent
            outputString += writeNumOfSpacesToString(currentNumSpaces)
            outputString += getIfStmtEnd(currentAstNode)
        elif (isElseStmtStart(currentAstNode) == True):
            currentNumSpaces -= numSpacesForIndent
            outputString += writeNumOfSpacesToString(currentNumSpaces)
            outputString += "}\n"
            outputString += writeNumOfSpacesToString(currentNumSpaces)
            outputString += getElseStmtStart(currentAstNode, config)
            currentNumSpaces += numSpacesForIndent
        elif (isUnnecessaryNode(currentAstNode) == True):
            continue
        elif (isNONENode(currentAstNode) == True):
            continue
        else:
            sys.exit("writeAstNodesToFile in SDLtoECConvert.py:  cannot handle this type of AST node (" + str(currentAstNode) + ").  Need to add logic to support it.")
        outputString += "\n"

    outputECFile.write(outputString)

def writeMessageAdditionToQueriedList(outputECFile, config):
    outputString = ""
    outputString += writeNumOfSpacesToString(numSpacesForIndent * 2)
    outputString += queriedName_EC + " " + assignmentOperator_EC + " "
    outputString += config.messageName_SDL + " " + appendOperator_EC + " "
    outputString += queriedName_EC + endOfLineOperator_EC + "\n"

    outputECFile.write(outputString)

def writeReturnValue(outputECFile, funcName, assignInfo):
    if (funcName not in assignInfo):
        sys.exit("writeReturnValue in SDLtoECConvert.py:  funcName parameter passed in is not in assignInfo parameter passed in.")

    if (outputKeyword not in assignInfo[funcName]):
        sys.exit("writeReturnValue in SDLtoECConvert.py:  outputKeyword not in assignInfo[funcName].")

    '''
    outputVarInfoObj = assignInfo[funcName][outputKeyword]

    outputVarDeps = outputVarInfoObj.getVarDeps()

    if ( (len(outputVarDeps) != 1) and (outputVarDeps != [trueKeyword_SDL, falseKeyword_SDL]) ):
        sys.exit("writeReturnValue in SDLtoECConvert.py:  variable dependencies of output keyword does not consist of a list of one element OR a list of [\"True\", \"False\"], which is what is expected.")
    '''

    outputString = ""
    outputString += writeNumOfSpacesToString(numSpacesForIndent * 2)
    outputString += returnKeyword_EC + " "

    '''
    if (len(outputVarDeps) == 1):
        outputString += str(outputVarDeps[0]) + endOfLineOperator_EC + "\n"
    else:
        outputString += outputKeyword + endOfLineOperator_EC + "\n"
    '''

    outputString += outputKeyword + endOfLineOperator_EC + "\n"

    outputECFile.write(outputString)

def writeFuncEnd(outputECFile):
    outputString = ""
    outputString += writeNumOfSpacesToString(numSpacesForIndent)
    outputString += funcEndChar_EC + "\n\n"

    outputECFile.write(outputString)

def addBoolRetVarForVerifyFunc(outputECFile):
    outputString = ""
    outputString += writeNumOfSpacesToString(numSpacesForIndent * 2)
    outputString += varKeyword_EC + " " + varNameForVerifyBoolRetVal_EC + " : "
    outputString += booleanType_EC + endOfLineOperator_EC + "\n"

    outputECFile.write(outputString)

def convertSignFunc(outputECFile, config, assignInfo, astNodes, generatorsList, pairingSetting):
    writeFuncDecl(outputECFile, config.signFuncName_SDL, signFuncName_EC, config, assignInfo, generatorsList, pairingSetting)
    writeVarDecls(outputECFile, config.signFuncName_SDL, assignInfo, config, generatorsList, [], pairingSetting)
    writeCountVarIncrement(outputECFile, signFuncName_EC)
    writeBodyOfFunc(outputECFile, config.signFuncName_SDL, astNodes, config, [], generatorsList)
    writeMessageAdditionToQueriedList(outputECFile, config)
    writeReturnValue(outputECFile, config.signFuncName_SDL, assignInfo)
    writeFuncEnd(outputECFile)

def convertVerifyFunc(outputECFile, config, assignInfo, astNodes, generatorsList, pairingSetting):
    writeFuncDecl(outputECFile, config.verifyFuncName_SDL, verifyFuncName_EC, config, assignInfo, generatorsList, pairingSetting)
    writeVarDecls(outputECFile, config.verifyFuncName_SDL, assignInfo, config, generatorsList, [], pairingSetting)
    #addBoolRetVarForVerifyFunc(outputECFile)
    writeCountVarIncrement(outputECFile, verifyFuncName_EC)
    writeBodyOfFunc(outputECFile, config.verifyFuncName_SDL, astNodes, config, [], generatorsList)
    writeReturnValue(outputECFile, config.verifyFuncName_SDL, assignInfo)
    writeFuncEnd(outputECFile)

def getTypeOfOutputVar(funcName, assignInfo, pairingSetting):
    '''
    inputOutputVarsDict = getInputOutputVarsDictOfFunc(funcName)
    outputVars = inputOutputVarsDict[outputKeyword]
    if (len(outputVars) != 1):
        sys.exit("getTypeOfOutputVar in SDLtoECConvert.py:  number of output variables of function is unequal to one; not supported.")

    if (outputVars[0] == "False"):
        return booleanType_EC

    outputType_EC = getVarTypeFromVarName_EC(outputVars[0], funcName)
    return outputType_EC
    '''
    if (funcName not in assignInfo):
        sys.exit("getTypeOfOutputVar in SDLtoECConvert.py:  function name parameter passed in is not in assignInfo parameter passed in.")

    if (outputKeyword not in assignInfo[funcName]):
        sys.exit("getTypeOfOutputVar in SDLtoECConvert.py:  output keyword is not in assignInfo[funcName] parameters passed in.")
 
    return getVarTypeFromVarName_EC(outputKeyword, funcName, pairingSetting)

def convertTypeSDLtoEC_Strings(outputType_SDL, pairingSetting):
    if (outputType_SDL == "G1"):
        return "G_1"
    if (outputType_SDL == "G2"):
        if (pairingSetting == config.symmetricPairingSettingKeyword_SDL):
            return "G_1"
        else:        
            return "G_2"
    if (outputType_SDL == "GT"):
        return "G_T"
    if (outputType_SDL == "ZR"):
        #return "Z_R"
        return "int"
    if (outputType_SDL == "int"):
        return "int"
    if (outputType_SDL == "bool"):
        return booleanType_EC

    sys.exit("convertTypeSDLtoEC_Strings in SDLtoECConvert.py:  outputType_SDL " + str(outputType_SDL) + " is not of a type we support; need to add more logic to support it.")

def convertTypeSDLtoEC(outputType_SDL, pairingSetting):
    if (outputType_SDL == types.G1):
        return "G_1"
    if (outputType_SDL == types.G2):
        if (pairingSetting == symmetricPairingSettingKeyword_SDL):
            return "G_1"
        else:
            return "G_2"
    if (outputType_SDL == types.GT):
        return "G_T"
    if (outputType_SDL == types.ZR):
        #return "Z_R"
        return "int"
    if (outputType_SDL == types.Int):
        return "int"
    if (outputType_SDL == types.bool):
        return booleanType_EC

    #this must be removed
    if (outputType_SDL == types.list):
        return "LISTLIST"

    sys.exit("convertTypeSDLtoEC in SDLtoECConvert.py:  outputType_SDL " + str(outputType_SDL) + " is not of a type we support; need to add more logic to support it.")

def writeFuncDecl(outputECFile, oldFuncName, newFuncName, config, assignInfo, generatorsList, pairingSetting):
    outputString = ""
    outputString += writeNumOfSpacesToString(numSpacesForIndent)
    outputString += funcName_EC + " " + newFuncName + "("
    outputString += getLineOfInputParams(oldFuncName, config, assignInfo, generatorsList, pairingSetting)
    outputString += ") : "
    outputString += getTypeOfOutputVar(oldFuncName, assignInfo, pairingSetting)
    outputString += " " + assignmentOperator_EC + " " + funcStartChar_EC + "\n"

    outputECFile.write(outputString)

def getLineOfInputParams(funcName, config, assignInfo, generatorsList, pairingSetting):
    inputOutputVarsDict = getInputOutputVarsDictOfFunc(funcName)

    publicKeyVars = getVarDeps(assignInfo, config, config.publicKeyName_SDL, config.keygenFuncName_SDL)
    secretKeyVars = getVarDeps(assignInfo, config, config.secretKeyName_SDL, config.keygenFuncName_SDL)
    
    outputString = ""

    for varName in inputOutputVarsDict[inputKeyword]:
        if DEBUG : print("getLineOfInputParams:  variable name is ", str(varName))

        # b/c our generators are generators, so no need to declare them here
        if (varName in generatorsList):
            continue

        # b/c public key variables are declared globally
        if (varName in publicKeyVars):
            continue

        if (varName == config.publicKeyName_SDL):
            continue

        # b/c secret key variables are declared globally
        if (varName in secretKeyVars):
            continue

        if (varName == config.secretKeyName_SDL):
            continue

        outputString += getECVarNameAndTypeFromSDLName(varName, config, assignInfo, funcName, pairingSetting)
        if (len(outputString) > 0):
            outputString += ", "

    lenOutputString = len(outputString)

    if (lenOutputString < 2):
        return outputString

    if (outputString[(lenOutputString - 2):lenOutputString] == ", "):
        outputString = outputString[0:(lenOutputString - len(", "))]

    return outputString

def getECVarNameAndTypeFromSDLName(varName, config, assignInfo, funcName, pairingSetting):

    if (funcName not in assignInfo):
        sys.exit("getECVarNameAndTypeFromSDLName in SDLtoECConvert.py:  funcName not in assignInfo.")

    #if (varName not in assignInfo[funcName][varName]):
        #sys.exit("getECVarNameAndTypeFromSDLName in SDLtoECConvert.py:  varName not in assignInfo[funcName].")

    #in EC, secret key is global, so no need to declare it here
    if (varName == config.secretKeyName_SDL):
        return ""

    if (varName == config.messageName_SDL):
        return config.messageName_SDL + " : " + messageType_EC

    if DEBUG : print("getECVarNameAndTypeFromSDLName:  varName and funcName are ", varName, " and ", funcName)

    varType_EC = getVarTypeFromVarName_EC(varName, funcName, pairingSetting)

    return varName + " : " + varType_EC

    sys.exit("getECVarNameAndTypeFromSDLName in SDLtoECConvert.py:  could not handle case of varName (" + str(varName) + ") passed in.  Need to add more logic for it.")

def addAdvAbstractDef(outputECFile, atLeastOneHashCall, assignInfo, config):
    outputString = ""
    outputString += writeNumOfSpacesToString(numSpacesForIndent)
    outputString += abstractKeyword_EC + " " + adversaryIdentifier_EC + " "
    outputString += assignmentOperator_EC + " " + adversarySignatureIdentifier_EC + funcStartChar_EC

    if (atLeastOneHashCall == True):
        outputString += hashFuncName_EC + ", "

    outputString += signFuncName_EC 

    extraFuncsForAdversary = getExtraFuncsForAdversary(assignInfo, config)

    if (len(extraFuncsForAdversary) == 0):
        outputString += funcEndChar_EC + "\n\n"
        outputECFile.write(outputString)
        return

    for extraFunc in extraFuncsForAdversary:
        outputString += ", "
        outputString += extraFunc

    outputString += funcEndChar_EC + "\n\n"
    outputECFile.write(outputString)

def writeVerifyArgsDeclForMain(outputECFile, config, assignInfo, generatorsList, pairingSetting):
    (justInputVarsForVerifyFunc, listOfVarsToNotDeclare) = getJustInputVarsForFunc(assignInfo, config, config.verifyFuncName_SDL, generatorsList)

    outputString = ""

    for inputVarName in justInputVarsForVerifyFunc:
        if (inputVarName in listOfVarsToNotDeclare):
            continue

        outputString += writeNumOfSpacesToString(numSpacesForIndent * 2)
        outputString += varKeyword_EC + " "
        outputString += getECVarNameAndTypeFromSDLName(inputVarName, config, assignInfo, config.verifyFuncName_SDL, pairingSetting)
        outputString += endOfLineOperator_EC + "\n"

    outputECFile.write(outputString)

def getJustInputVarsForFunc(assignInfo, config, funcName, generatorsList):
    publicKeyVars = getVarDeps(assignInfo, config, config.publicKeyName_SDL, config.keygenFuncName_SDL)
    secretKeyVars = getVarDeps(assignInfo, config, config.secretKeyName_SDL, config.keygenFuncName_SDL)

    listOfVarsToNotDeclare = []

    for publicKeyVar in publicKeyVars:
        if (publicKeyVar not in listOfVarsToNotDeclare):
            listOfVarsToNotDeclare.append(publicKeyVar)

    if (config.publicKeyName_SDL not in listOfVarsToNotDeclare):
        listOfVarsToNotDeclare.append(config.publicKeyName_SDL)

    for secretKeyVar in secretKeyVars:
        if (secretKeyVar not in listOfVarsToNotDeclare):
            listOfVarsToNotDeclare.append(secretKeyVar)

    if (config.secretKeyName_SDL not in listOfVarsToNotDeclare):
        listOfVarsToNotDeclare.append(config.secretKeyName_SDL)

    for generatorVar in generatorsList:
        if (generatorVar not in listOfVarsToNotDeclare):
            listOfVarsToNotDeclare.append(generatorVar)

    if (outputKeyword not in listOfVarsToNotDeclare):
        listOfVarsToNotDeclare.append(outputKeyword)

    if (funcName not in assignInfo):
        sys.exit("getJustInputVarsForFunc in SDLtoECConvert.py:  function name parameter passed in is not in assignInfo.")

    if (inputKeyword not in assignInfo[funcName]):
        sys.exit("getJustInputVarsForFunc in SDLtoECConvert.py:  input keyword is not in assignInfo[funcName parameter passed in].")

    inputVarInfoObj = assignInfo[funcName][inputKeyword]
    
    if (inputVarInfoObj == None):
        sys.exit("getJustInputVarsForFunc in SDLtoECConvert.py:  input variable information object extracted from assignInfo[funcName] is None.")

    inputVarNamesList = []

    if ( (inputVarInfoObj.getIsList() == True) and (len(inputVarInfoObj.getListNodesList()) > 0) ):
        for inputVarName in inputVarInfoObj.getListNodesList():
            if (inputVarName in inputVarNamesList):
                sys.exit("getJustInputVarsForFunc in SDLtoECConvert.py:  duplicate variable names found in input variable names.")

            inputVarNamesList.append(inputVarName)

    return (inputVarNamesList, listOfVarsToNotDeclare)

def writeMainFunc(outputECFile, config, assignInfo, astNodes, atLeastOneHashCall, generatorsList, pairingSetting):
    outputString = ""
    outputString += writeNumOfSpacesToString(numSpacesForIndent)
    outputString += funcName_EC + " Main() : " + booleanType_EC + " " + assignmentOperator_EC + " "
    outputString += funcStartChar_EC + "\n"
    outputECFile.write(outputString)

    writeVerifyArgsDeclForMain(outputECFile, config, assignInfo, generatorsList, pairingSetting)
    writeExtraVarsNeededForMain(outputECFile, config, assignInfo)
    writeCallToInit(outputECFile)
    writeCallToAbstractAdversaryFunction(outputECFile, config, assignInfo)
    writeCallToVerify(outputECFile, assignInfo, config, generatorsList)
    writeReturnStatementForMain(outputECFile, config)
    writeEndOfMain(outputECFile)

def writeEndOfMain(outputECFile):
    outputString = ""
    outputString += writeNumOfSpacesToString(numSpacesForIndent)
    outputString += funcEndChar_EC + "\n" + funcEndChar_EC + gameEndChar_EC + "\n"

    outputECFile.write(outputString)

def writeReturnStatementForMain(outputECFile, config):
    outputString = ""
    outputString += writeNumOfSpacesToString(numSpacesForIndent * 2)
    outputString += returnKeyword_EC + " " + vVarInMain_EC + " " + andOperator_EC + " " + notOperator_EC
    outputString += memKeyword_EC + "(" + config.messageName_SDL + ", " + queriedName_EC + ")"
    outputString += endOfLineOperator_EC + "\n"

    outputECFile.write(outputString)

def writeCallToVerify(outputECFile, assignInfo, config, generatorsList):
    outputString = ""
    outputString += writeNumOfSpacesToString(numSpacesForIndent * 2)
    outputString += vVarInMain_EC + " " + assignmentOperator_EC + " " + verifyFuncName_EC + "("
    (inputVarsList, listOfVarsToNotDeclare) = getJustInputVarsForFunc(assignInfo, config, config.verifyFuncName_SDL, generatorsList)
    for inputVar in inputVarsList:
        if (inputVar not in listOfVarsToNotDeclare):
            outputString += inputVar + ", "

    lengthOfNewOutputString = len(outputString) - len(", ")

    outputString = outputString[0:lengthOfNewOutputString]

    outputString += ")" + endOfLineOperator_EC + "\n"

    outputECFile.write(outputString)

def writeCallToAbstractAdversaryFunction(outputECFile, config, assignInfo):
    outputString = ""
    outputString += writeNumOfSpacesToString(numSpacesForIndent * 2)
    outputString += "(" + config.messageName_SDL + ", " + config.signatureVarName_SDL + ") "
    outputString += assignmentOperator_EC
    #outputString += " " + adversaryIdentifier_EC + "(" + config.publicKeyName_SDL + ");\n\n"
    outputString += " " + adversaryIdentifier_EC + "("

    publicKeyVars = getVarDeps(assignInfo, config, config.publicKeyName_SDL, config.keygenFuncName_SDL)

    for publicKeyVar in publicKeyVars:
        outputString += publicKeyVar + ", "

    lenOutputString = len(outputString)

    outputString = outputString[0:(lenOutputString - len(", "))]
    outputString += ");\n\n"

    #outputString += writeNumOfSpacesToString(numSpacesForIndent * 2)

    outputECFile.write(outputString)

def writeCallToInit(outputECFile):
    outputString = ""
    outputString += writeNumOfSpacesToString(numSpacesForIndent * 2)
    outputString += dummyVarInMain_EC + " " + assignmentOperator_EC + " " + initFuncName_EC 
    outputString += "();\n"

    outputECFile.write(outputString)

def writeExtraVarsNeededForMain(outputECFile, config, assignInfo):
    outputString = ""
    #outputString += writeNumOfSpacesToString(numSpacesForIndent * 2)
    #outputString += varKeyword_EC + " " + sVarInMain_EC + " : "
    #groupTypeOfSignatureVariable = getGroupTypeOfSignatureVariable(outputECFile, assignInfo, config)
    #outputString += groupTypeOfSignatureVariable + ";\n"
    outputString += writeNumOfSpacesToString(numSpacesForIndent * 2)
    outputString += varKeyword_EC + " " + vVarInMain_EC + " : " + booleanType_EC + ";\n"
    outputString += writeNumOfSpacesToString(numSpacesForIndent * 2)
    outputString += varKeyword_EC + " " + dummyVarInMain_EC + " : " + booleanType_EC + ";\n\n"

    outputECFile.write(outputString)

def initializeCountVars(outputECFile, config, assignInfo):
    allFuncsWithCountVars = getExtraFuncsForAdversary(assignInfo, config)
    allFuncsWithCountVars.append(hashFuncName_EC)
    allFuncsWithCountVars.append(signFuncName_EC)
    allFuncsWithCountVars.append(verifyFuncName_EC)

    outputString = ""

    for funcName in allFuncsWithCountVars:
        outputString += writeNumOfSpacesToString(numSpacesForIndent * 2)
        outputString += countVarPrefix + funcName + " = 0;\n"

    outputECFile.write(outputString)

def writeInitFunc(outputECFile, config, assignInfo, astNodes, atLeastOneHashCall, generatorsList, pairingSetting):
    outputString = ""
    outputString += writeNumOfSpacesToString(numSpacesForIndent)
    outputString += funcName_EC + " Init() : " + booleanType_EC + " = {\n"

    outputECFile.write(outputString)

    writeVarDecls(outputECFile, config.keygenFuncName_SDL, assignInfo, config, generatorsList, [outputKeyword], pairingSetting)

    initializeCountVars(outputECFile, config, assignInfo)

    writeBodyOfFunc(outputECFile, config.keygenFuncName_SDL, astNodes, config, [outputKeyword], generatorsList)

    #convertKeygenFunc(outputECFile, config, assignInfo, astNodes, generatorsList)

    outputString = ""

    if (atLeastOneHashCall == True):
        outputString += writeNumOfSpacesToString(numSpacesForIndent * 2)
        outputString += randomOracleVarName_EC + " " + assignmentOperator_EC + " " + emptyMapName_EC
        outputString += endOfLineOperator_EC + "\n"
        outputString += writeNumOfSpacesToString(numSpacesForIndent * 2)
        outputString += queriedName_EC + " " + assignmentOperator_EC + " " + emptyMapSymbol_EC
        outputString += endOfLineOperator_EC + "\n"
        outputECFile.write(outputString)

    outputString = ""
    outputString += writeNumOfSpacesToString(numSpacesForIndent * 2)
    outputString += returnKeyword_EC + " " + trueKeyword_EC + endOfLineOperator_EC + "\n"
    outputString += writeNumOfSpacesToString(numSpacesForIndent)
    outputString += funcEndChar_EC + "\n\n"
    outputECFile.write(outputString)

def convertKeygenFunc(outputECFile, config, assignInfo, astNodes, generatorsList):

    '''
    # public key variables and secret key variables are all declared globally, so don't declare them
    # locally in the Keygen function.

    publicKeyVars = getVarDeps(assignInfo, config, config.publicKeyName_SDL, config.keygenFuncName_SDL)
    secretKeyVars = getVarDeps(assignInfo, config, config.secretKeyName_SDL, config.keygenFuncName_SDL)

    listOfVarsToNotDeclare = []

    for publicKeyVar in publicKeyVars:
        if (publicKeyVar not in listOfVarsToNotDeclare):
            listOfVarsToNotDeclare.append(publicKeyVar)

    for secretKeyVar in secretKeyVars:
        if (secretKeyVar not in listOfVarsToNotDeclare):
            listOfVarsToNotDeclare.append(secretKeyVar)

    if (outputKeyword not in listOfVarsToNotDeclare):
        listOfVarsToNotDeclare.append(outputKeyword)

    if (config.publicKeyName_SDL not in listOfVarsToNotDeclare):
        listOfVarsToNotDeclare.append(config.publicKeyName_SDL)

    if (config.secretKeyName_SDL not in listOfVarsToNotDeclare):
        listOfVarsToNotDeclare.append(config.secretKeyName_SDL)
    '''

    writeVarDecls(outputECFile, config.keygenFuncName_SDL, assignInfo, config, generatorsList, [])
    writeBodyOfFunc(outputECFile, config.keygenFuncName_SDL, astNodes, config, [outputKeyword], generatorsList)

def getGroupTypeOfSignatureVariable(outputECFile, assignInfo, config, pairingSetting):
    if (config.signFuncName_SDL not in assignInfo):
        sys.exit("getGroupTypeOfSignatureVariable in SDLtoECConvert.py:  the function name of the sign function from the config file is not in assignInfo.")

    if (outputKeyword not in assignInfo[config.signFuncName_SDL]):
        sys.exit("getGroupTypeOfSignatureVariable in SDLtoECConvert.py:  output keyword is not in assignInfo[config.signFuncName_SDL].")

    varDepsOfOutputKeyword = assignInfo[config.signFuncName_SDL][outputKeyword].getVarDeps()
    if (len(varDepsOfOutputKeyword) != 1):
        sys.exit("getGroupTypeOfSignatureVariable in SDLtoECConvert.py:  length of variable dependencies list of output variable is unequal to 1 (currently unsupported).")

    outputVariable = varDepsOfOutputKeyword[0]
    if (outputVariable not in assignInfo[config.signFuncName_SDL]):
        sys.exit("getGroupTypeOfSignatureVariable in SDLtoECConvert.py:  output variable found is not assigned anywhere in the sign function.")

    return getVarTypeFromVarName_EC(outputVariable, config.signFuncName_SDL, pairingSetting)

#def getSubFuncsThatEachFuncCallsRecursive(assignInfo, funcName, config, retDict):
    #if (funcName not in assignInfo):
        #sys.exit("getSubFuncsThatEachFuncCallsRecursive in SDLtoECConvert.py:  function name passed in is not in assignInfo structure passed in.")

def getFuncCallsInThisAssignNodeRecursive(currentAssignNode, retList):
    if (currentAssignNode == None):
        return

    if (currentAssignNode.type == ops.FUNC):
        userFuncName = getFullVarName(currentAssignNode, True)
        if (userFuncName not in retList):
            retList.append(userFuncName)

    if (currentAssignNode.left != None):
        getFuncCallsInThisAssignNodeRecursive(currentAssignNode.left, retList)
    if (currentAssignNode.right != None):
        getFuncCallsInThisAssignNodeRecursive(currentAssignNode.right, retList)

def getFuncCallsInThisAssignNode(currentAssignNode):
    retList = []

    getFuncCallsInThisAssignNodeRecursive(currentAssignNode, retList)

    return retList

def parseAssignInfoForFuncCallsInOneFunc(assignInfo, funcName, config):
    if (funcName not in assignInfo):
        sys.exit("parseAssignInfoForFuncCallsInOneFunc in SDLtoECConvert.py:  function name passed in is not in assignInfo structure passed in.")

    retList = []

    for varName in assignInfo[funcName]:
        varInfoObj = assignInfo[funcName][varName]
        currentAssignNode = varInfoObj.getAssignNode()
        funcCallsInThisAssignNode = getFuncCallsInThisAssignNode(currentAssignNode)
        for currentFuncCall in funcCallsInThisAssignNode:
            if (currentFuncCall not in retList):
                retList.append(currentFuncCall)

    return retList

def getSubFuncsThatEachFuncCalls(assignInfo, config):
    retDict = {}

    for funcName in assignInfo:
        retDict[funcName] = parseAssignInfoForFuncCallsInOneFunc(assignInfo, funcName, config)
        #getSubFuncsThatEachFuncCallsRecursive(assignInfo, funcName, config, retDict)

    return retDict

def convertSubFuncsStructIntoFullyRecursiveChainRecursive(subFuncsStruct, funcName, retListForThisFunc, funcsAlreadyCovered):
    for funcThatIsCalled in subFuncsStruct[funcName]:
        if (funcThatIsCalled not in retListForThisFunc):
            retListForThisFunc.append(funcThatIsCalled)

        if (funcThatIsCalled not in funcsAlreadyCovered):
            convertSubFuncsStructIntoFullyRecursiveChainRecursive(subFuncsStruct, funcThatIsCalled, retListForThisFunc, funcsAlreadyCovered)
            funcsAlreadyCovered.append(funcThatIsCalled)

def convertSubFuncsStructIntoFullyRecursiveChain(subFuncsStruct):
    retDict = {}

    for funcName in subFuncsStruct:
        retListForThisFunc = []
        convertSubFuncsStructIntoFullyRecursiveChainRecursive(subFuncsStruct, funcName, retListForThisFunc, [])
        retDict[funcName] = retListForThisFunc

    return retDict

def getExtraFuncsForAdversary(assignInfo, config):
    # the adversary gets access to all functions except for those that are only called from the sign
    # function.  So first determine which functions each function calls, then determine which functions
    # are only called by sign

    # determine which functions each function calls
    subFuncsThatEachFuncCalls = getSubFuncsThatEachFuncCalls(assignInfo, config)

    # now convert it into a fully recursive chain (i.e., unroll each function call into all function calls
    # that that function makes)
    subFuncsInFullyRecursiveChain = convertSubFuncsStructIntoFullyRecursiveChain(subFuncsThatEachFuncCalls)
    #print(subFuncsInFullyRecursiveChain)

    #STARTHEREDDDDDDDD

    if (config.signFuncName_SDL not in subFuncsInFullyRecursiveChain):
        sys.exit("getExtraFuncsForAdversary in SDLtoECConvert.py:  sign function name specified in config file isn't in list of sub-functions in fully recursive chain.")

    funcsThatSignFuncCalls = copy.deepcopy(subFuncsInFullyRecursiveChain[config.signFuncName_SDL])

    #print(funcsThatSignFuncCalls)

    # get rid of any functions that are called by functions other than sign
    #for currentFuncName in subFuncsInFullyRecursiveChain:

    # this part I'm not crazy about.  Basically, we're saying keygen, verify, and sign are the main
    # functions of any signature scheme.  Nothing else (not even a setup function).  So we only
    # allow the adversary to have access to functions that are keygen, verify, or any function that either
    # of them calls.  If only sign calls it, the adversary doesn't get access to it.
    for currentFuncName in [config.keygenFuncName_SDL, config.verifyFuncName_SDL]:
        #if (currentFuncName == config.signFuncName_SDL):
            #continue

        # the following for loops assumes no duplicates in subFuncsInFullyRecursiveChain, which in its
        # current form guarantees
        for subFuncThatIsCalled in subFuncsInFullyRecursiveChain[currentFuncName]:
            if (subFuncThatIsCalled in funcsThatSignFuncCalls):
                funcsThatSignFuncCalls.remove(subFuncThatIsCalled)

    retList = []

    # don't include any functions that are only called by sign
    # funcsThatSignFuncCalls now only stores functions that are called by sign exclusively
    for keyName in assignInfo:
        if ( (keyName not in funcsThatSignFuncCalls) and (keyName not in funcNamesAdvDoesntNeed) and (keyName != config.keygenFuncName_SDL) and (keyName != config.signFuncName_SDL) and (keyName != config.verifyFuncName_SDL) ):
            if (keyName not in retList):
                retList.append(keyName)

    #print(retList)

    return retList

def getHashGroupTypeOfNodeRecursive(inputNode, hashesGroupTypesInFunc):
    if (inputNode.type == ops.HASH):
        groupTypeToAdd = str(inputNode.right)
        if (len(hashesGroupTypesInFunc) == 0):
            hashesGroupTypesInFunc.append(groupTypeToAdd)
        else:
            if (groupTypeToAdd not in hashesGroupTypesInFunc):
                sys.exit("getHashGroupTypeOfNodeRecursive in SDLtoECConvert.py:  found mismatching hash types in same function.")

    if (inputNode.left != None):
        getHashGroupTypeOfNodeRecursive(inputNode.left, hashesGroupTypesInFunc)

    if (inputNode.right != None):
        getHashGroupTypeOfNodeRecursive(inputNode.right, hashesGroupTypesInFunc)

def getHashGroupTypeOfNode(inputNode, hashesGroupTypesInFunc):
    getHashGroupTypeOfNodeRecursive(inputNode, hashesGroupTypesInFunc)

def getHashGroupTypeOfFunc(funcName, assignInfo, config):
    if (funcName not in assignInfo):
        sys.exit("getHashGroupTypeOfFunc in SDLtoECConvert.py:  function name parameter passed in isn't in assignInfo parameter passed in.")

    hashesGroupTypesInFunc = []

    for varName in assignInfo[funcName]:
        varInfoObj = assignInfo[funcName][varName]
        assignNodeRight = varInfoObj.getAssignNode().right
        hashGroupTypeOfNode = getHashGroupTypeOfNode(assignNodeRight, hashesGroupTypesInFunc)

    if (len(hashesGroupTypesInFunc) > 1):
        sys.exit("getHashGroupTypeOfFunc in SDLtoECConvert.py:  length of hashesGroupTypesInFunc data structure returned is greater than one.")

    if (len(hashesGroupTypesInFunc) == 0):
        return None

    return hashesGroupTypesInFunc[0]

def getInputVarsForFunc(outputECFile, assignInfo, config, funcName, generatorsList):
    if (funcName not in assignInfo):
        sys.exit("getInputVarsForFunc in SDLtoECConvert.py:  function name passed in is not in assignInfo parameter passed in.")

    outputString = ""

    inputOutputVarsDict = getInputOutputVarsDictOfFunc(funcName)

    publicKeyVars = getVarDeps(assignInfo, config, config.publicKeyName_SDL, config.keygenFuncName_SDL)
    secretKeyVars = getVarDeps(assignInfo, config, config.secretKeyName_SDL, config.keygenFuncName_SDL)
    
    for varName in inputOutputVarsDict[inputKeyword]:
        # b/c our generators are generators, so no need to declare them here
        if (varName in generatorsList):
            continue

        # b/c public key variables are declared globally
        if (varName in publicKeyVars):
            continue

        if (varName == config.publicKeyName_SDL):
            continue

        # b/c secret key variables are declared globally
        if (varName in secretKeyVars):
            continue

        #in EC, secret key is global, so no need to declare it here
        if (varName == config.secretKeyName_SDL):
            continue

        if (varName == config.messageName_SDL):
            outputString += messageType_EC + ", "
            continue

        varType_EC = getVarTypeFromVarName_EC(varName, funcName)
        outputString += varType_EC + ", "

    lenOutputString = len(outputString)
    outputString = outputString[0:(lenOutputString - len(", "))]

    return outputString

def addAdversaryDeclLineToOutputECFile(outputECFile, assignInfo, config, generatorsList, pairingSetting):
    groupTypeOfSignatureVariable = getGroupTypeOfSignatureVariable(outputECFile, assignInfo, config, pairingSetting)

    extraFuncsForAdversary = getExtraFuncsForAdversary(assignInfo, config)

    #(adv_public_key_1 : G_1, adv_public_key _2 : int)

    outputString = ""
    outputString += adversaryKeyword_EC + " " + adversaryVarName_EC + " (" # + advPubKeyVarName_EC + " : ("

    #pubKeyType = getVarTypeFromVarName_EC(config.publicKeyName_SDL, config.keygenFuncName_SDL)

    publicKeyVars = getVarDeps(assignInfo, config, config.publicKeyName_SDL, config.keygenFuncName_SDL)

    counterForAdvPubKeyDecls = 1

    for publicKeyVar in publicKeyVars:
        outputString += advPubKeyVarName_EC + "_" + str(counterForAdvPubKeyDecls) + " : "
        currentPublicKeyVarType = getVarTypeFromVarName_EC(publicKeyVar, config.keygenFuncName_SDL, pairingSetting)
        outputString += currentPublicKeyVarType + ", "
        counterForAdvPubKeyDecls += 1

    lenOutputString = len(outputString)
    outputString = outputString[0:(lenOutputString - len(", "))]

    outputString += ") : (" + messageType_EC + " * " + groupTypeOfSignatureVariable + ") {"
    outputString += messageType_EC + " -> "

    hashGroupTypeOfSigFunc_SDL = getHashGroupTypeOfFunc(config.signFuncName_SDL, assignInfo, config)
    hashGroupTypeOfSigFunc_EC = convertTypeSDLtoEC_Strings(hashGroupTypeOfSigFunc_SDL, pairingSetting)

    outputString += hashGroupTypeOfSigFunc_EC + "; ("

    outputECFile.write(outputString)
    outputString = ""

    # write input vars for sign function
    outputString += getInputVarsForFunc(outputECFile, assignInfo, config, config.signFuncName_SDL, generatorsList)

    outputString += ") -> "

    outputTypeOfSignFunc = getTypeOfOutputVar(config.signFuncName_SDL, assignInfo, pairingSetting)
    outputString += outputTypeOfSignFunc

    outputECFile.write(outputString)
    outputString = ""

    if (len(extraFuncsForAdversary) == 0):
        outputString += "}."
        outputString += "\n\n"
        outputECFile.write(outputString)
        return

    for extraFunc in extraFuncsForAdversary:
        outputString += "; ("
        outputString += getInputVarsForFunc(outputECFile, assignInfo, config, extraFunc, generatorsList)
        outputString += ") -> "
        outputTypeOfFunc = getTypeOfOutputVar(extraFunc, assignInfo, pairingSetting)
        outputString += outputTypeOfFunc

    outputString += "}.\n\n"

    outputECFile.write(outputString)

def writeExtraFuncsForAdversary(outputECFile, assignInfo, config, astNodes, generatorsList, pairingSetting):
    extraFuncsForAdversary = getExtraFuncsForAdversary(assignInfo, config)

    if (len(extraFuncsForAdversary) == 0):
        return

    for extraFunc in extraFuncsForAdversary:
        writeFuncDecl(outputECFile, extraFunc, extraFunc, config, assignInfo, generatorsList, pairingSetting)
        writeVarDecls(outputECFile, extraFunc, assignInfo, config, generatorsList, [], pairingSetting)
        writeCountVarIncrement(outputECFile, extraFunc)
        writeBodyOfFunc(outputECFile, extraFunc, astNodes, config, [], generatorsList)
        writeReturnValue(outputECFile, extraFunc, assignInfo)
        writeFuncEnd(outputECFile)

def addCountVars(outputECFile, assignInfo, config, atLeastOneHashCall):
    outputString = ""

    allFuncsWithCountVars = getExtraFuncsForAdversary(assignInfo, config)

    currentNumSpacesToUse = numSpacesForIndent

    if (atLeastOneHashCall == True):
        outputString += writeNumOfSpacesToString(currentNumSpacesToUse)
        outputString += varKeyword_EC + " " + countVarPrefix + hashFuncName_EC + " : " + intType_EC + "\n"

    allFuncsWithCountVars.append(signFuncName_EC)
    allFuncsWithCountVars.append(verifyFuncName_EC)

    for countVarFuncName in allFuncsWithCountVars:
        outputString += writeNumOfSpacesToString(currentNumSpacesToUse)
        outputString += varKeyword_EC + " " + countVarPrefix + countVarFuncName + " : " + intType_EC + "\n"

    outputECFile.write(outputString)

def writeCountVarIncrement(outputECFile, funcName):
    outputString = ""
    currentNumSpacesToUse = 4
    outputString += writeNumOfSpacesToString(currentNumSpacesToUse)
    outputString += countVarPrefix + funcName + " " + assignmentOperator_EC + " "
    outputString += countVarPrefix + funcName + " " + additionOperator_EC + " 1;\n"
    outputECFile.write(outputString)

def getGeneratorsList(assignInfo, config):
    if (NONE_FUNC_NAME not in assignInfo):
        return []

    if (config.generatorKeyword_SDL not in assignInfo[NONE_FUNC_NAME]):
        return []

    return assignInfo[NONE_FUNC_NAME][config.generatorKeyword_SDL].getVarDeps()

def getPairingSetting(assignInfo, config):
    if (NONE_FUNC_NAME not in assignInfo):
        sys.exit("getPairingSetting in SDLtoECConvert.py:  no NONE_FUNC_NAME entries in assignInfo.")

    if (config.pairingSettingKeyword_SDL not in assignInfo[NONE_FUNC_NAME]):
        sys.exit("getPairingSetting in SDLtoECConvert.py:  the pairing setting keyword specified in the config file isn't in assignInfo[NONE_FUNC_NAME].")

    pairingSettingList = assignInfo[NONE_FUNC_NAME][config.pairingSettingKeyword_SDL].getVarDeps()

    if (len(pairingSettingList) != 1):
        sys.exit("getPairingSetting in SDLtoECConvert.py:  length of Var Deps list of assignInfo[NONE_FUNC_NAME][config.pairingSettingKeyword_SDL] is unequal to one, which is what is expected.")

    pairingSetting = pairingSettingList[0]

    if ( (pairingSetting != symmetricPairingSettingKeyword_SDL) and (pairingSetting != asymmetricPairingSettingKeyword_SDL) ):
        sys.exit("getPairingSetting in SDLtoECConvert.py:  pairing setting obtained is neither \"symmetric\" nor \"asymmetric\".")

    #print(pairingSetting)

    return pairingSetting

def getGroupTypeOfHashStatements(assignInfo, config):
    ddddd

def main(inputSDLFileName, configName, outputECFileName, debugOrNot):
    global DEBUG

    if (debugOrNot == "True"):
        DEBUG = True
    elif (debugOrNot == "False"):
        DEBUG = False
    else:
        sys.exit("main in SDLtoECConvert.py:  DEBUG parameter from command line was specified incorrectly (two options are True and False).")


    inputSDLFile = open(inputSDLFileName, 'r')
    outputECFile = open(outputECFileName, 'w')

    config = importlib.import_module(configName)

    atLeastOneHashCall = False

    (assignInfo, astNodes) = getInputSDLFileMetadata(inputSDLFileName)

    pairingSetting = getPairingSetting(assignInfo, config)

    generatorsList = getGeneratorsList(assignInfo, config)

    addTemplateLinesToOutputECFile_SymmetricOrAsymmetric(outputECFile, assignInfo, generatorsList, pairingSetting, config)

    addAdversaryDeclLineToOutputECFile(outputECFile, assignInfo, config, generatorsList, pairingSetting)

    addGameDeclLine(inputSDLFileName, outputECFile)
    addGlobalVars(outputECFile, assignInfo, config, generatorsList, pairingSetting)

    atLeastOneHashCall = getAtLeastOneHashCallOrNot_WithSDLParser(assignInfo)

    addCountVars(outputECFile, assignInfo, config, atLeastOneHashCall)

    if (atLeastOneHashCall == True):
        groupTypeOfHashStatements = getGroupTypeOfHashStatements(assignInfo, config)
        addStatementsForPresenceOfHashes(outputECFile, assignInfo, config, pairingSetting)

    convertSignFunc(outputECFile, config, assignInfo, astNodes, generatorsList, pairingSetting)

    writeExtraFuncsForAdversary(outputECFile, assignInfo, config, astNodes, generatorsList, pairingSetting)

    addAdvAbstractDef(outputECFile, atLeastOneHashCall, assignInfo, config)

    convertVerifyFunc(outputECFile, config, assignInfo, astNodes, generatorsList, pairingSetting)

    writeInitFunc(outputECFile, config, assignInfo, astNodes, atLeastOneHashCall, generatorsList, pairingSetting)

    writeMainFunc(outputECFile, config, assignInfo, astNodes, atLeastOneHashCall, generatorsList, pairingSetting)

    #convertKeygenFunc(outputECFile, config, assignInfo, astNodes)

    inputSDLFile.close()
    outputECFile.close()

def printErrorMessageAndExit():
    sys.exit("Usage:  python " + sys.argv[0] + " [name of input SDL file] [SCHEMENAME.config] [name of output EasyCrypt file] [Print DEBUG info (True or False)]]")

if __name__ == "__main__":
    lenSysArgv = len(sys.argv)

    if ( (lenSysArgv < 5) or (lenSysArgv > 5) ):
        printErrorMessageAndExit()

    if ( (sys.argv[1] == "-help") or (sys.argv[1] == "--help") ):
        printErrorMessageAndExit()

    main(sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4])
