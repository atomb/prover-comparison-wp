AGDAOPTS=-i . -i ${HOME}/.agda/lib-0.6/src

all: WPSound.agdai

%.agdai: %.agda
	agda ${AGDAOPTS} $<

clean:
	rm -f *.agdai
