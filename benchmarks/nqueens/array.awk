BEGIN { FS="\t" }
/begin-benchmark/ {
  NAME=$2

  # set ONLYSML and/or NOSML with (awk -v NOSML=1)
  if (ONLYSML && $2 !~ /SML/) { KEEP=0; next }
  if (NOSML && $2 ~ /SML/) { KEEP=0; next }

  KEEP=1
}
/header/ && KEEP { print "\\textbf{"$2"}" }
/point/ && KEEP {
  SEC=int($3)/1000
  if (SEC < 60) {
    TIME=SEC"s"
  } else {
    TIME=int(SEC/60)"m"(SEC-60)"s"
  }
  print "& "TIME
}
/end-benchmark/ && KEEP { print "\\\\" }