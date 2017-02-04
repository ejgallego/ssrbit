set terminal postscript portrait enhanced mono dashed lw 1 "Helvetica" 14  size 8,4
set output "queens.ps"

set xrange [0:17]
set logscale y

set xlabel 'Number of queens'
set ylabel 'Time in ms. (log-scale)'

set key inside left top

set style line 1 lc rgb 'black' pt 5   # square
set style line 2 lc rgb 'black' pt 7   # circle
set style line 3 lc rgb 'black' pt 9   # triangle

plot "queens_c.dat" using 1:2 title 'C' with points linestyle 1,      \
     "queens_ml.dat" using 1:2 title 'OCaml' with points linestyle 2, \
     "queens_coq.dat" using 1:2 title 'Coq' with points linestyle 3