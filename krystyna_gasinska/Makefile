GHC        = ghc
HAPPY      = happy
HAPPY_OPTS = --array --info --ghc --coerce
ALEX       = alex
ALEX_OPTS  = --ghc
BUILD_DIR  = build
SOURCE_DIR = source

.PHONY : all clean distclean

all : interpreter

%.hs : %.y
	${HAPPY} ${HAPPY_OPTS} -o ${SOURCE_DIR}/$@ $<

%.hs : %.x
	${ALEX} ${ALEX_OPTS} -o ${SOURCE_DIR}/$@ $<

interpreter : ${SOURCE_DIR}/AbsGrammar.hs ${SOURCE_DIR}/SkelGrammar.hs ${SOURCE_DIR}/LexGrammar.hs ${SOURCE_DIR}/ParGrammar.hs ${SOURCE_DIR}/PrintGrammar.hs ${SOURCE_DIR}/Parse.hs ${SOURCE_DIR}/Interpreter.hs
	mkdir -p ${BUILD_DIR}
	${GHC} ${GHC_OPTS} -outputdir ${BUILD_DIR} -o interpreter $^

clean :
	-rm -f interpreter
	-rm -rf ${BUILD_DIR}