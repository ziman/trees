all: dispatch.gif logtree.gif

dispatch.gif: dispatch-00.png
	convert -delay 75 dispatch-*.png -coalesce -layers OptimizeFrame -dither FloydSteinberg -colors 4 dispatch.gif

dispatch-00.png: dispatch-anim
	for i in `seq -w 0 80`; do ./dispatch-anim $$i && mv frame.png dispatch-$$i.png; done

dispatch-anim: dispatch-anim.hs
	ghc --make -O2 -o dispatch-anim dispatch-anim.hs

logtree.gif: logtree-00.png
	convert -delay 75 logtree-*.png -coalesce -layers OptimizeFrame -dither FloydSteinberg -colors 4 logtree.gif

logtree-00.png: logtree-anim
	for i in `seq -w 0 129`; do ./logtree-anim $$i && mv frame.png logtree-$$i.png; done

logtree-anim: logtree-anim.hs
	ghc --make -O2 -o logtree-anim logtree-anim.hs

clean:
	-rm -f *.o *.hi *.gif *.png dispatch-anim logtree-anim
