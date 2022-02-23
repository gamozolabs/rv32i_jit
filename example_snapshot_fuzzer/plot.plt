set term wxt size 1440,900 persist
set logscale x
set grid mxtics mytics xtics ytics
set xlabel "Time"
set ylabel "Coverage"
plot "graph.txt" u 1:2 w l

