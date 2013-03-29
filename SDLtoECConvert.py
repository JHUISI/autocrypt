import sdlpath
from sdlparser.SDLParser import *
import re, importlib

templateFileName = "ECTemplate.txt"
configFileName = "SDLtoECConfig"
hashFuncName_EC = "Hash"
signFuncName_EC = "Sign"
messageName_EC = "m"
messageType_EC = "message"
secretKeyName_EC = "secret_key"
multOp_EC = "*"
expOp_EC = "^"

def writeNumOfSpacesToString(numSpaces):
    outputString = ""

    for space in range(0, numSpaces):
        outputString += " "

    return outputString

def addTemplateLinesToOutputECFile(outputECFile):
    templateFile = open(templateFileName, 'r')
    outputString = ""

    for templateLine in templateFile:
        outputString += templateLine

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
    outputString += "_EF = {\n"

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

def addGlobalVars(outputECFile):
    outputString = "  var " + secretKeyName_EC + " : int\n"
    outputString += "  var queried : message list\n"
    outputECFile.write(outputString)

def addGlobalVarsForHashes(outputECFile):
    outputString = "  var rand_oracle : (message, G_1) map\n"
    outputECFile.write(outputString)

def addHashFuncDef(outputECFile):
    outputString = "\n  fun "+ hashFuncName_EC + "(m : message) : G_1 = {\n"
    outputString += "    if(!in_dom(m, rand_oracle)) {\n"
    outputString += "      rand_oracle[m] = Rand_G_1();\n"
    outputString += "    }\n"
    outputString += "    return rand_oracle[m];\n"
    outputString += "  }\n\n"

    outputECFile.write(outputString)

def addStatementsForPresenceOfHashes(outputECFile):
    addGlobalVarsForHashes(outputECFile)
    addHashFuncDef(outputECFile)

def getInputSDLFileMetadata(inputSDLFileName):
    parseFile2(inputSDLFileName, False, True)
    assignInfo = getAssignInfo()
    astNodes = getAstNodes()
    return (assignInfo, astNodes)

def getAtLeastOneHashCallOrNot_WithSDLParser(assignInfo):
    for funcName in assignInfo:
        for varName in assignInfo[funcName]:
            varInfoObj = assignInfo[funcName][varName]
            if (len(varInfoObj.getHashArgsInAssignNode()) > 0):
                return True

    return False

def writeVarDecls(outputECFile, oldFuncName, assignInfo):
    if (oldFuncName not in assignInfo):
        sys.exit("writeVarDecls in SDLtoECConvert.py:  oldFuncName not in assignInfo.")

    outputString = ""

    for varName in assignInfo[oldFuncName]:
        if ( (varName == inputKeyword) or (varName == outputKeyword) ):
            continue

        varType_SDL = getVarTypeFromVarName(varName, oldFuncName, False, False)
        varType_EC = convertGroupTypeSDLtoEC(varType_SDL)

        outputString += "    var " + varName + " : " + varType_EC + ";\n"

    if (len(outputString) > 0):
        outputECFile.write(outputString)

def writeBodyOfFunc(outputECFile, oldFuncName, astNodes):
    startLineNoOfFunc = getStartLineNoOfFunc(oldFuncName)
    endLineNoOfFunc = getEndLineNoOfFunc(oldFuncName)

    startLineNoOfBody = startLineNoOfFunc + 2
    endLineNoOfBody = endLineNoOfFunc - 2

    writeAstNodesToFile(outputECFile, astNodes, startLineNoOfBody, endLineNoOfBody)

def isAssignStmt(astNode):
    if (astNode.type == ops.EQ):
        return True

    return False

def getAssignStmtAsString(astNode):
    if (astNode.type == ops.ATTR):
        return str(astNode)
    elif (astNode.type == ops.EXP):
        leftSide = getAssignStmtAsString(astNode.left)
        rightSide = getAssignStmtAsString(astNode.right)
        return "(" + leftSide + " ^ " + rightSide + ")"
    else:
        sys.exit("getAssignStmtAsString in SDLtoECConvert.py:  could not handle this type of node (" + str(astNode) + ").  Need to add more logic to support it.")

def writeAstNodesToFile(outputECFile, astNodes, startLineNo, endLineNo):
    outputString = ""
    currentNumSpaces = 4

    for lineNo in range(startLineNo, (endLineNo + 1)):
        currentAstNode = astNodes[(lineNo - 1)]
        outputString += writeNumOfSpacesToString(currentNumSpaces)
        if (isAssignStmt(currentAstNode) == True):
            outputString += getAssignStmtAsString(currentAstNode)
        else:
            sys.exit("writeAstNodesToFile in SDLtoECConvert.py:  cannot handle this type of AST node.  Need to add logic to support it.")
        outputString += "\n"

    outputECFile.write(outputString)

def convertSignFunc(outputECFile, config, assignInfo, astNodes):
    writeFuncDecl(outputECFile, config.signFuncName_SDL, signFuncName_EC, config)
    writeVarDecls(outputECFile, config.signFuncName_SDL, assignInfo)
    writeBodyOfFunc(outputECFile, config.signFuncName_SDL, astNodes)

def getTypeOfOutputVar(funcName):
    inputOutputVarsDict = getInputOutputVarsDictOfFunc(funcName)
    outputVars = inputOutputVarsDict[outputKeyword]
    if (len(outputVars) != 1):
        sys.exit("getTypeOfOutputVar in SDLtoECConvert.py:  number of output variables of function is unequal to one; not supported.")

    outputType_SDL = getVarTypeFromVarName(outputVars[0], funcName, False, False)
    outputType_EC = convertGroupTypeSDLtoEC(outputType_SDL)
    return outputType_EC

def convertGroupTypeSDLtoEC(outputType_SDL):
    if (outputType_SDL == types.G1):
        return "G_1"
    if (outputType_SDL == types.G2):
        return "G_1"
    if (outputType_SDL == types.GT):
        return "G_T"

    sys.exit("convertGroupTypeSDLtoEC in SDLtoECConvert.py:  outputType_SDL is not of a type we support; need to add more logic to support it.")

def writeFuncDecl(outputECFile, oldFuncName, newFuncName, config):
    outputString = ""
    outputString += "  fun " + newFuncName + "("
    outputString += getLineOfInputParams(oldFuncName, config)
    outputString += ") : "
    outputString += getTypeOfOutputVar(oldFuncName)
    outputString += " = {\n"

    outputECFile.write(outputString)

def getLineOfInputParams(funcName, config):
    inputOutputVarsDict = getInputOutputVarsDictOfFunc(funcName)
    
    outputString = ""

    for varName in inputOutputVarsDict[inputKeyword]:
        outputString += getECVarNameAndTypeFromSDLName(varName, config)
        if (len(outputString) > 0):
            outputString += ", "

    lenOutputString = len(outputString)

    if (outputString[(lenOutputString - 2):lenOutputString] == ", "):
        outputString = outputString[0:(lenOutputString - len(", "))]

    return outputString

def getECVarNameAndTypeFromSDLName(varName, config):
    if (varName == config.secretKeyName_SDL):
        return ""

    if (varName == config.messageName_SDL):
        return messageName_EC + " : " + messageType_EC

    sys.exit("getECVarNameAndTypeFromSDLName in SDLtoECConvert.py:  could not handle case of varName passed in.  Need to add more logic for it.")

def main(inputSDLFileName, outputECFileName):
    inputSDLFile = open(inputSDLFileName, 'r')
    outputECFile = open(outputECFileName, 'w')

    config = importlib.import_module(configFileName)

    atLeastOneHashCall = False

    (assignInfo, astNodes) = getInputSDLFileMetadata(inputSDLFileName)

    addTemplateLinesToOutputECFile(outputECFile)
    addGameDeclLine(inputSDLFileName, outputECFile)
    addGlobalVars(outputECFile)

    atLeastOneHashCall = getAtLeastOneHashCallOrNot_WithSDLParser(assignInfo)
    if (atLeastOneHashCall == True):
        addStatementsForPresenceOfHashes(outputECFile)

    convertSignFunc(outputECFile, config, assignInfo, astNodes)

    inputSDLFile.close()
    outputECFile.close()

if __name__ == "__main__":
    lenSysArgv = len(sys.argv)

    if ( (lenSysArgv < 3) or (lenSysArgv > 3) ):
        sys.exit("Usage:  python " + sys.argv[0] + " [name of input SDL file] [name of output EasyCrypt file]")

    if ( (sys.argv[1] == "-help") or (sys.argv[1] == "--help") ):
        sys.exit("Usage:  python " + sys.argv[0] + " [name of input SDL file] [name of output EasyCrypt file]")

    main(sys.argv[1], sys.argv[2])
