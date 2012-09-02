#!/usr/bin/awk -f
BEGIN { num = 0; baseline = 0 }
{
    if (num == 0) {
        num = $1
    } else {
    if (baseline == 0) {
        baseline = ($1+$2+$3+$4+$5)/num; print "Baseline: " baseline
    } else {
        if ($1 == 0) {
            print $2
        } else {
            avg = ($2+$3+$4+$5+$6)/num;
            print "(" $1 "," baseline/avg ")"
        }
    }
}
}
