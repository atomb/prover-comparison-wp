SOURCES = Assertion.idr \
          Command.idr \
          Expr.idr \
          WP.idr \
          Axiomatic.idr \
          Eval.idr \
          WPSound.idr
IBCFILES = $(patsubst %.idr, %.ibc, $(SOURCES))

all:
	idris --check WPSound.idr

clean:
	rm -f $(IBCFILES)
