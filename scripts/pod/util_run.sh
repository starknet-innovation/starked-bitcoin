#!/usr/bin/env bash
# GPU-UTIL measurement: the sample with the stage output, at two --jobs settings, with nvidia-smi at 100 ms.
source /root/pod/env.sh
cd $SRC
bin=$SRC/zig-out/bin/cuda-epoch
run() { name=$1; shift
  d=$WORK/$name; rm -rf $d; mkdir -p $d; ln -s $DATA/sample/blocks $d/blocks; ln -s $DATA/sample/undo $d/undo
  nvidia-smi --query-gpu=timestamp,utilization.gpu,utilization.memory,power.draw,memory.used --format=csv,noheader,nounits -lms 100 > $LOGS/$name.smi.csv &
  smi=$!
  /usr/bin/time -v $bin $DATA/headers.bin $d - $DATA/chain.sbchain --heights $DATA/sample/heights.txt "$@" > $LOGS/$name.log 2>&1; rc=$?
  kill $smi
  echo "== $name exit $rc"; grep -E "^(standalone|proving thread|  L |  stages|  [0-9]+ blocks deferred)|rror" $LOGS/$name.log | cut -c1-400
  awk -F', ' '{u+=$2;m+=$3;p+=$4;n++} END{if(n) printf "   smi mean: gpu %.0f%% mem %.0f%% power %.0f W (%d samples)\n",u/n,m/n,p/n,n}' $LOGS/$name.smi.csv
  [ -f $d/deferred-931850.txt ] && cp $d/deferred-931850.txt $LOGS/$name.deferred.txt
  rm -rf $d/proofs
}
run util-j3 --jobs 3
run util-j8 --jobs 8
echo UTIL_DONE
