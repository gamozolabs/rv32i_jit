set term wxt size 1440,900 persist
set logscale x
set grid mxtics mytics xtics ytics

set multiplot layout 1,2

set xlabel "Time (seconds)"
set ylabel "Coverage"
plot "graph.txt" u 1:3 w l

set xlabel "Fuzz Cases"
set ylabel "Coverage"
plot "graph.txt" u 2:3 w l

