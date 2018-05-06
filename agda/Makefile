AGDAOPTS=-i . -i ${HOME}/.agda/lib-0.6/src

all: Axiomatic.agdai

%.agdai: %.agda
	agda ${AGDAOPTS} $<

clean:
	rm -f *.agdai
