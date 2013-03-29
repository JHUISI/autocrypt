import sdlpath
from sdlparser.SDLParser import *
import re, importlib

templateFileName = "ECTemplate.txt"
configFileName = "SDLtoECConfig"
hashFuncName = "Hash"

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
    outputString = "  var secret_key : int\n"
    outputString += "  var queried : message list\n"
    outputECFile.write(outputString)

def addGlobalVarsForHashes(outputECFile):
    outputString = "  var rand_oracle : (message, G_1) map\n"
    outputECFile.write(outputString)

def addHashFuncDef(outputECFile):
    outputString = "\n  fun "+ hashFuncName + "(m : message) : G_1 = {\n"
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
    return assignInfo

def getAtLeastOneHashCallOrNot_WithSDLParser(assignInfo):
    for funcName in assignInfo:
        for varName in assignInfo[funcName]:
            varInfoObj = assignInfo[funcName][varName]
            if (len(varInfoObj.getHashArgsInAssignNode()) > 0):
                return True

    return False

def convertSignFunc(outputECFile):
    outputString = ""
    outputString += "  fun Sign("

    outputECFile.write(outputString)

def main(inputSDLFileName, outputECFileName):
    inputSDLFile = open(inputSDLFileName, 'r')
    outputECFile = open(outputECFileName, 'w')

    config = importlib.import_module(configFileName)

    atLeastOneHashCall = False

    assignInfo = getInputSDLFileMetadata(inputSDLFileName)

    addTemplateLinesToOutputECFile(outputECFile)
    addGameDeclLine(inputSDLFileName, outputECFile)
    addGlobalVars(outputECFile)

    atLeastOneHashCall = getAtLeastOneHashCallOrNot_WithSDLParser(assignInfo)
    if (atLeastOneHashCall == True):
        addStatementsForPresenceOfHashes(outputECFile)

    convertSignFunc(outputECFile)

    inputSDLFile.close()
    outputECFile.close()

if __name__ == "__main__":
    lenSysArgv = len(sys.argv)

    if ( (lenSysArgv < 3) or (lenSysArgv > 3) ):
        sys.exit("Usage:  python " + sys.argv[0] + " [name of input SDL file] [name of output EasyCrypt file]")

    if ( (sys.argv[1] == "-help") or (sys.argv[1] == "--help") ):
        sys.exit("Usage:  python " + sys.argv[0] + " [name of input SDL file] [name of output EasyCrypt file]")

    main(sys.argv[1], sys.argv[2])
