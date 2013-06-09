ghc --make -O2 dispatch-anim.hs -o dispatch-anim
for i in {00..80}; do
    echo $i
    ./dispatch-anim $i
    mv frame.png disp-$i.png
done
convert disp-*.png disp.gif

