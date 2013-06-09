all: dispatch.gif

dispatch.gif: dispatch-00.png
	convert dispatch-*.png dispatch.gif

dispatch-00.png: dispatch-anim
	for i in `seq 00 80`; do ./dispatch-anim $$i && mv frame.png dispatch-$$i.png; done

dispatch-anim: dispatch-anim.hs
	ghc --make -O2 -o dispatch-anim dispatch-anim.hs

clean:
	-rm -f *.o *.hi *.gif *.png dispatch-anim
