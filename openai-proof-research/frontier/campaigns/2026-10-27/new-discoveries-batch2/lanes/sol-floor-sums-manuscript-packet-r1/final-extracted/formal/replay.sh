#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1
G="${HELPER_GUARD:-$PWD/helper_guard.py}"
mkdir -p logs
python "$G" python lean_guard.py logs/SemBase.log -o SemBase.olean SemBase.lean >logs/SemBase.console 2>&1
echo SemBase OK
python "$G" python lean_guard.py logs/Sem000.log -o Sem000.olean Sem000.lean >logs/Sem000.console 2>&1
echo Sem000 OK
python "$G" python lean_guard.py logs/Sem001.log -o Sem001.olean Sem001.lean >logs/Sem001.console 2>&1
echo Sem001 OK
python "$G" python lean_guard.py logs/Sem002.log -o Sem002.olean Sem002.lean >logs/Sem002.console 2>&1
echo Sem002 OK
python "$G" python lean_guard.py logs/Sem003.log -o Sem003.olean Sem003.lean >logs/Sem003.console 2>&1
echo Sem003 OK
python "$G" python lean_guard.py logs/Sem004.log -o Sem004.olean Sem004.lean >logs/Sem004.console 2>&1
echo Sem004 OK
python "$G" python lean_guard.py logs/Sem005.log -o Sem005.olean Sem005.lean >logs/Sem005.console 2>&1
echo Sem005 OK
python "$G" python lean_guard.py logs/Sem006.log -o Sem006.olean Sem006.lean >logs/Sem006.console 2>&1
echo Sem006 OK
python "$G" python lean_guard.py logs/Sem007.log -o Sem007.olean Sem007.lean >logs/Sem007.console 2>&1
echo Sem007 OK
python "$G" python lean_guard.py logs/Sem008.log -o Sem008.olean Sem008.lean >logs/Sem008.console 2>&1
echo Sem008 OK
python "$G" python lean_guard.py logs/Sem009.log -o Sem009.olean Sem009.lean >logs/Sem009.console 2>&1
echo Sem009 OK
python "$G" python lean_guard.py logs/Sem010.log -o Sem010.olean Sem010.lean >logs/Sem010.console 2>&1
echo Sem010 OK
python "$G" python lean_guard.py logs/Sem011.log -o Sem011.olean Sem011.lean >logs/Sem011.console 2>&1
echo Sem011 OK
python "$G" python lean_guard.py logs/Sem012.log -o Sem012.olean Sem012.lean >logs/Sem012.console 2>&1
echo Sem012 OK
python "$G" python lean_guard.py logs/Sem013.log -o Sem013.olean Sem013.lean >logs/Sem013.console 2>&1
echo Sem013 OK
python "$G" python lean_guard.py logs/Sem014.log -o Sem014.olean Sem014.lean >logs/Sem014.console 2>&1
echo Sem014 OK
python "$G" python lean_guard.py logs/Sem015.log -o Sem015.olean Sem015.lean >logs/Sem015.console 2>&1
echo Sem015 OK
python "$G" python lean_guard.py logs/Sem016.log -o Sem016.olean Sem016.lean >logs/Sem016.console 2>&1
echo Sem016 OK
python "$G" python lean_guard.py logs/Sem017.log -o Sem017.olean Sem017.lean >logs/Sem017.console 2>&1
echo Sem017 OK
python "$G" python lean_guard.py logs/Sem018.log -o Sem018.olean Sem018.lean >logs/Sem018.console 2>&1
echo Sem018 OK
python "$G" python lean_guard.py logs/Sem019.log -o Sem019.olean Sem019.lean >logs/Sem019.console 2>&1
echo Sem019 OK
python "$G" python lean_guard.py logs/Sem020.log -o Sem020.olean Sem020.lean >logs/Sem020.console 2>&1
echo Sem020 OK
python "$G" python lean_guard.py logs/Sem021.log -o Sem021.olean Sem021.lean >logs/Sem021.console 2>&1
echo Sem021 OK
python "$G" python lean_guard.py logs/Sem022.log -o Sem022.olean Sem022.lean >logs/Sem022.console 2>&1
echo Sem022 OK
python "$G" python lean_guard.py logs/Sem023.log -o Sem023.olean Sem023.lean >logs/Sem023.console 2>&1
echo Sem023 OK
python "$G" python lean_guard.py logs/Sem024.log -o Sem024.olean Sem024.lean >logs/Sem024.console 2>&1
echo Sem024 OK
python "$G" python lean_guard.py logs/Sem025.log -o Sem025.olean Sem025.lean >logs/Sem025.console 2>&1
echo Sem025 OK
python "$G" python lean_guard.py logs/Sem026.log -o Sem026.olean Sem026.lean >logs/Sem026.console 2>&1
echo Sem026 OK
python "$G" python lean_guard.py logs/Sem027.log -o Sem027.olean Sem027.lean >logs/Sem027.console 2>&1
echo Sem027 OK
python "$G" python lean_guard.py logs/Sem028.log -o Sem028.olean Sem028.lean >logs/Sem028.console 2>&1
echo Sem028 OK
python "$G" python lean_guard.py logs/Sem029.log -o Sem029.olean Sem029.lean >logs/Sem029.console 2>&1
echo Sem029 OK
python "$G" python lean_guard.py logs/Sem030.log -o Sem030.olean Sem030.lean >logs/Sem030.console 2>&1
echo Sem030 OK
python "$G" python lean_guard.py logs/Sem031.log -o Sem031.olean Sem031.lean >logs/Sem031.console 2>&1
echo Sem031 OK
python "$G" python lean_guard.py logs/Sem032.log -o Sem032.olean Sem032.lean >logs/Sem032.console 2>&1
echo Sem032 OK
python "$G" python lean_guard.py logs/Sem033.log -o Sem033.olean Sem033.lean >logs/Sem033.console 2>&1
echo Sem033 OK
python "$G" python lean_guard.py logs/Sem034.log -o Sem034.olean Sem034.lean >logs/Sem034.console 2>&1
echo Sem034 OK
python "$G" python lean_guard.py logs/Sem035.log -o Sem035.olean Sem035.lean >logs/Sem035.console 2>&1
echo Sem035 OK
python "$G" python lean_guard.py logs/Sem036.log -o Sem036.olean Sem036.lean >logs/Sem036.console 2>&1
echo Sem036 OK
python "$G" python lean_guard.py logs/Sem037.log -o Sem037.olean Sem037.lean >logs/Sem037.console 2>&1
echo Sem037 OK
python "$G" python lean_guard.py logs/Sem038.log -o Sem038.olean Sem038.lean >logs/Sem038.console 2>&1
echo Sem038 OK
python "$G" python lean_guard.py logs/Sem039.log -o Sem039.olean Sem039.lean >logs/Sem039.console 2>&1
echo Sem039 OK
python "$G" python lean_guard.py logs/Sem040.log -o Sem040.olean Sem040.lean >logs/Sem040.console 2>&1
echo Sem040 OK
python "$G" python lean_guard.py logs/Sem041.log -o Sem041.olean Sem041.lean >logs/Sem041.console 2>&1
echo Sem041 OK
python "$G" python lean_guard.py logs/Sem042.log -o Sem042.olean Sem042.lean >logs/Sem042.console 2>&1
echo Sem042 OK
python "$G" python lean_guard.py logs/Sem043.log -o Sem043.olean Sem043.lean >logs/Sem043.console 2>&1
echo Sem043 OK
python "$G" python lean_guard.py logs/Sem044.log -o Sem044.olean Sem044.lean >logs/Sem044.console 2>&1
echo Sem044 OK
python "$G" python lean_guard.py logs/Sem045.log -o Sem045.olean Sem045.lean >logs/Sem045.console 2>&1
echo Sem045 OK
python "$G" python lean_guard.py logs/Sem046.log -o Sem046.olean Sem046.lean >logs/Sem046.console 2>&1
echo Sem046 OK
python "$G" python lean_guard.py logs/Sem047.log -o Sem047.olean Sem047.lean >logs/Sem047.console 2>&1
echo Sem047 OK
python "$G" python lean_guard.py logs/Sem048.log -o Sem048.olean Sem048.lean >logs/Sem048.console 2>&1
echo Sem048 OK
python "$G" python lean_guard.py logs/Sem049.log -o Sem049.olean Sem049.lean >logs/Sem049.console 2>&1
echo Sem049 OK
python "$G" python lean_guard.py logs/Sem050.log -o Sem050.olean Sem050.lean >logs/Sem050.console 2>&1
echo Sem050 OK
python "$G" python lean_guard.py logs/Sem051.log -o Sem051.olean Sem051.lean >logs/Sem051.console 2>&1
echo Sem051 OK
python "$G" python lean_guard.py logs/Sem052.log -o Sem052.olean Sem052.lean >logs/Sem052.console 2>&1
echo Sem052 OK
python "$G" python lean_guard.py logs/Sem053.log -o Sem053.olean Sem053.lean >logs/Sem053.console 2>&1
echo Sem053 OK
python "$G" python lean_guard.py logs/Sem054.log -o Sem054.olean Sem054.lean >logs/Sem054.console 2>&1
echo Sem054 OK
python "$G" python lean_guard.py logs/Sem055.log -o Sem055.olean Sem055.lean >logs/Sem055.console 2>&1
echo Sem055 OK
python "$G" python lean_guard.py logs/Sem056.log -o Sem056.olean Sem056.lean >logs/Sem056.console 2>&1
echo Sem056 OK
python "$G" python lean_guard.py logs/Sem057.log -o Sem057.olean Sem057.lean >logs/Sem057.console 2>&1
echo Sem057 OK
python "$G" python lean_guard.py logs/Sem058.log -o Sem058.olean Sem058.lean >logs/Sem058.console 2>&1
echo Sem058 OK
python "$G" python lean_guard.py logs/Sem059.log -o Sem059.olean Sem059.lean >logs/Sem059.console 2>&1
echo Sem059 OK
python "$G" python lean_guard.py logs/Sem060.log -o Sem060.olean Sem060.lean >logs/Sem060.console 2>&1
echo Sem060 OK
python "$G" python lean_guard.py logs/Sem061.log -o Sem061.olean Sem061.lean >logs/Sem061.console 2>&1
echo Sem061 OK
python "$G" python lean_guard.py logs/Sem062.log -o Sem062.olean Sem062.lean >logs/Sem062.console 2>&1
echo Sem062 OK
python "$G" python lean_guard.py logs/Sem063.log -o Sem063.olean Sem063.lean >logs/Sem063.console 2>&1
echo Sem063 OK
python "$G" python lean_guard.py logs/Sem064.log -o Sem064.olean Sem064.lean >logs/Sem064.console 2>&1
echo Sem064 OK
python "$G" python lean_guard.py logs/Sem065.log -o Sem065.olean Sem065.lean >logs/Sem065.console 2>&1
echo Sem065 OK
python "$G" python lean_guard.py logs/Sem066.log -o Sem066.olean Sem066.lean >logs/Sem066.console 2>&1
echo Sem066 OK
python "$G" python lean_guard.py logs/Sem067.log -o Sem067.olean Sem067.lean >logs/Sem067.console 2>&1
echo Sem067 OK
python "$G" python lean_guard.py logs/Query.log -o Query.olean Query.lean >logs/Query.console 2>&1
echo Query OK
python "$G" python lean_guard.py logs/Reduction.log -o Reduction.olean Reduction.lean >logs/Reduction.console 2>&1
echo Reduction OK
python "$G" python lean_guard.py logs/ClipBridge.log -o ClipBridge.olean ClipBridge.lean >logs/ClipBridge.console 2>&1
echo ClipBridge OK
python "$G" python lean_guard.py logs/Dag000.log -o Dag000.olean Dag000.lean >logs/Dag000.console 2>&1
echo Dag000 OK
python "$G" python lean_guard.py logs/Dag001.log -o Dag001.olean Dag001.lean >logs/Dag001.console 2>&1
echo Dag001 OK
python "$G" python lean_guard.py logs/Dag002.log -o Dag002.olean Dag002.lean >logs/Dag002.console 2>&1
echo Dag002 OK
python "$G" python lean_guard.py logs/Dag003.log -o Dag003.olean Dag003.lean >logs/Dag003.console 2>&1
echo Dag003 OK
python "$G" python lean_guard.py logs/Dag004.log -o Dag004.olean Dag004.lean >logs/Dag004.console 2>&1
echo Dag004 OK
python "$G" python lean_guard.py logs/Dag005.log -o Dag005.olean Dag005.lean >logs/Dag005.console 2>&1
echo Dag005 OK
python "$G" python lean_guard.py logs/Dag006.log -o Dag006.olean Dag006.lean >logs/Dag006.console 2>&1
echo Dag006 OK
python "$G" python lean_guard.py logs/Dag007.log -o Dag007.olean Dag007.lean >logs/Dag007.console 2>&1
echo Dag007 OK
python "$G" python lean_guard.py logs/Dag008.log -o Dag008.olean Dag008.lean >logs/Dag008.console 2>&1
echo Dag008 OK
python "$G" python lean_guard.py logs/Dag009.log -o Dag009.olean Dag009.lean >logs/Dag009.console 2>&1
echo Dag009 OK
python "$G" python lean_guard.py logs/Dag010.log -o Dag010.olean Dag010.lean >logs/Dag010.console 2>&1
echo Dag010 OK
python "$G" python lean_guard.py logs/Dag011.log -o Dag011.olean Dag011.lean >logs/Dag011.console 2>&1
echo Dag011 OK
python "$G" python lean_guard.py logs/Dag012.log -o Dag012.olean Dag012.lean >logs/Dag012.console 2>&1
echo Dag012 OK
python "$G" python lean_guard.py logs/Dag013.log -o Dag013.olean Dag013.lean >logs/Dag013.console 2>&1
echo Dag013 OK
python "$G" python lean_guard.py logs/Dag014.log -o Dag014.olean Dag014.lean >logs/Dag014.console 2>&1
echo Dag014 OK
python "$G" python lean_guard.py logs/Dag015.log -o Dag015.olean Dag015.lean >logs/Dag015.console 2>&1
echo Dag015 OK
python "$G" python lean_guard.py logs/Dag016.log -o Dag016.olean Dag016.lean >logs/Dag016.console 2>&1
echo Dag016 OK
python "$G" python lean_guard.py logs/Dag017.log -o Dag017.olean Dag017.lean >logs/Dag017.console 2>&1
echo Dag017 OK
python "$G" python lean_guard.py logs/Dag018.log -o Dag018.olean Dag018.lean >logs/Dag018.console 2>&1
echo Dag018 OK
python "$G" python lean_guard.py logs/Dag019.log -o Dag019.olean Dag019.lean >logs/Dag019.console 2>&1
echo Dag019 OK
python "$G" python lean_guard.py logs/Dag020.log -o Dag020.olean Dag020.lean >logs/Dag020.console 2>&1
echo Dag020 OK
python "$G" python lean_guard.py logs/Dag021.log -o Dag021.olean Dag021.lean >logs/Dag021.console 2>&1
echo Dag021 OK
python "$G" python lean_guard.py logs/Dag022.log -o Dag022.olean Dag022.lean >logs/Dag022.console 2>&1
echo Dag022 OK
python "$G" python lean_guard.py logs/Dag023.log -o Dag023.olean Dag023.lean >logs/Dag023.console 2>&1
echo Dag023 OK
python "$G" python lean_guard.py logs/Dag024.log -o Dag024.olean Dag024.lean >logs/Dag024.console 2>&1
echo Dag024 OK
python "$G" python lean_guard.py logs/Dag025.log -o Dag025.olean Dag025.lean >logs/Dag025.console 2>&1
echo Dag025 OK
python "$G" python lean_guard.py logs/Dag026.log -o Dag026.olean Dag026.lean >logs/Dag026.console 2>&1
echo Dag026 OK
python "$G" python lean_guard.py logs/generated.th_lemma_0.log -o generated/th_lemma_0.olean generated/th_lemma_0.lean >logs/generated.th_lemma_0.console 2>&1
echo generated.th_lemma_0 OK
python "$G" python lean_guard.py logs/Dag027.log -o Dag027.olean Dag027.lean >logs/Dag027.console 2>&1
echo Dag027 OK
python "$G" python lean_guard.py logs/Dag028.log -o Dag028.olean Dag028.lean >logs/Dag028.console 2>&1
echo Dag028 OK
python "$G" python lean_guard.py logs/Dag029.log -o Dag029.olean Dag029.lean >logs/Dag029.console 2>&1
echo Dag029 OK
python "$G" python lean_guard.py logs/Dag030.log -o Dag030.olean Dag030.lean >logs/Dag030.console 2>&1
echo Dag030 OK
python "$G" python lean_guard.py logs/Dag031.log -o Dag031.olean Dag031.lean >logs/Dag031.console 2>&1
echo Dag031 OK
python "$G" python lean_guard.py logs/Dag032.log -o Dag032.olean Dag032.lean >logs/Dag032.console 2>&1
echo Dag032 OK
python "$G" python lean_guard.py logs/Dag033.log -o Dag033.olean Dag033.lean >logs/Dag033.console 2>&1
echo Dag033 OK
python "$G" python lean_guard.py logs/generated.th_lemma_1.log -o generated/th_lemma_1.olean generated/th_lemma_1.lean >logs/generated.th_lemma_1.console 2>&1
echo generated.th_lemma_1 OK
python "$G" python lean_guard.py logs/Dag034.log -o Dag034.olean Dag034.lean >logs/Dag034.console 2>&1
echo Dag034 OK
python "$G" python lean_guard.py logs/Dag035.log -o Dag035.olean Dag035.lean >logs/Dag035.console 2>&1
echo Dag035 OK
python "$G" python lean_guard.py logs/Dag036.log -o Dag036.olean Dag036.lean >logs/Dag036.console 2>&1
echo Dag036 OK
python "$G" python lean_guard.py logs/Dag037.log -o Dag037.olean Dag037.lean >logs/Dag037.console 2>&1
echo Dag037 OK
python "$G" python lean_guard.py logs/Dag038.log -o Dag038.olean Dag038.lean >logs/Dag038.console 2>&1
echo Dag038 OK
python "$G" python lean_guard.py logs/Dag039.log -o Dag039.olean Dag039.lean >logs/Dag039.console 2>&1
echo Dag039 OK
python "$G" python lean_guard.py logs/Dag040.log -o Dag040.olean Dag040.lean >logs/Dag040.console 2>&1
echo Dag040 OK
python "$G" python lean_guard.py logs/Dag041.log -o Dag041.olean Dag041.lean >logs/Dag041.console 2>&1
echo Dag041 OK
python "$G" python lean_guard.py logs/Dag042.log -o Dag042.olean Dag042.lean >logs/Dag042.console 2>&1
echo Dag042 OK
python "$G" python lean_guard.py logs/Dag043.log -o Dag043.olean Dag043.lean >logs/Dag043.console 2>&1
echo Dag043 OK
python "$G" python lean_guard.py logs/Dag044.log -o Dag044.olean Dag044.lean >logs/Dag044.console 2>&1
echo Dag044 OK
python "$G" python lean_guard.py logs/Dag045.log -o Dag045.olean Dag045.lean >logs/Dag045.console 2>&1
echo Dag045 OK
python "$G" python lean_guard.py logs/Dag046.log -o Dag046.olean Dag046.lean >logs/Dag046.console 2>&1
echo Dag046 OK
python "$G" python lean_guard.py logs/Dag047.log -o Dag047.olean Dag047.lean >logs/Dag047.console 2>&1
echo Dag047 OK
python "$G" python lean_guard.py logs/Dag048.log -o Dag048.olean Dag048.lean >logs/Dag048.console 2>&1
echo Dag048 OK
python "$G" python lean_guard.py logs/Dag049.log -o Dag049.olean Dag049.lean >logs/Dag049.console 2>&1
echo Dag049 OK
python "$G" python lean_guard.py logs/Dag050.log -o Dag050.olean Dag050.lean >logs/Dag050.console 2>&1
echo Dag050 OK
python "$G" python lean_guard.py logs/Dag051.log -o Dag051.olean Dag051.lean >logs/Dag051.console 2>&1
echo Dag051 OK
python "$G" python lean_guard.py logs/Dag052.log -o Dag052.olean Dag052.lean >logs/Dag052.console 2>&1
echo Dag052 OK
python "$G" python lean_guard.py logs/Dag053.log -o Dag053.olean Dag053.lean >logs/Dag053.console 2>&1
echo Dag053 OK
python "$G" python lean_guard.py logs/Dag054.log -o Dag054.olean Dag054.lean >logs/Dag054.console 2>&1
echo Dag054 OK
python "$G" python lean_guard.py logs/Dag055.log -o Dag055.olean Dag055.lean >logs/Dag055.console 2>&1
echo Dag055 OK
python "$G" python lean_guard.py logs/Dag056.log -o Dag056.olean Dag056.lean >logs/Dag056.console 2>&1
echo Dag056 OK
python "$G" python lean_guard.py logs/Dag057.log -o Dag057.olean Dag057.lean >logs/Dag057.console 2>&1
echo Dag057 OK
python "$G" python lean_guard.py logs/Dag058.log -o Dag058.olean Dag058.lean >logs/Dag058.console 2>&1
echo Dag058 OK
python "$G" python lean_guard.py logs/Dag059.log -o Dag059.olean Dag059.lean >logs/Dag059.console 2>&1
echo Dag059 OK
python "$G" python lean_guard.py logs/Dag060.log -o Dag060.olean Dag060.lean >logs/Dag060.console 2>&1
echo Dag060 OK
python "$G" python lean_guard.py logs/Dag061.log -o Dag061.olean Dag061.lean >logs/Dag061.console 2>&1
echo Dag061 OK
python "$G" python lean_guard.py logs/Dag062.log -o Dag062.olean Dag062.lean >logs/Dag062.console 2>&1
echo Dag062 OK
python "$G" python lean_guard.py logs/Dag063.log -o Dag063.olean Dag063.lean >logs/Dag063.console 2>&1
echo Dag063 OK
python "$G" python lean_guard.py logs/Dag064.log -o Dag064.olean Dag064.lean >logs/Dag064.console 2>&1
echo Dag064 OK
python "$G" python lean_guard.py logs/Dag065.log -o Dag065.olean Dag065.lean >logs/Dag065.console 2>&1
echo Dag065 OK
python "$G" python lean_guard.py logs/generated.th_lemma_2.log -o generated/th_lemma_2.olean generated/th_lemma_2.lean >logs/generated.th_lemma_2.console 2>&1
echo generated.th_lemma_2 OK
python "$G" python lean_guard.py logs/Dag066.log -o Dag066.olean Dag066.lean >logs/Dag066.console 2>&1
echo Dag066 OK
python "$G" python lean_guard.py logs/generated.th_lemma_3.log -o generated/th_lemma_3.olean generated/th_lemma_3.lean >logs/generated.th_lemma_3.console 2>&1
echo generated.th_lemma_3 OK
python "$G" python lean_guard.py logs/Dag067.log -o Dag067.olean Dag067.lean >logs/Dag067.console 2>&1
echo Dag067 OK
python "$G" python lean_guard.py logs/Dag068.log -o Dag068.olean Dag068.lean >logs/Dag068.console 2>&1
echo Dag068 OK
python "$G" python lean_guard.py logs/Dag069.log -o Dag069.olean Dag069.lean >logs/Dag069.console 2>&1
echo Dag069 OK
python "$G" python lean_guard.py logs/Dag070.log -o Dag070.olean Dag070.lean >logs/Dag070.console 2>&1
echo Dag070 OK
python "$G" python lean_guard.py logs/Dag071.log -o Dag071.olean Dag071.lean >logs/Dag071.console 2>&1
echo Dag071 OK
python "$G" python lean_guard.py logs/Dag072.log -o Dag072.olean Dag072.lean >logs/Dag072.console 2>&1
echo Dag072 OK
python "$G" python lean_guard.py logs/Dag073.log -o Dag073.olean Dag073.lean >logs/Dag073.console 2>&1
echo Dag073 OK
python "$G" python lean_guard.py logs/Dag074.log -o Dag074.olean Dag074.lean >logs/Dag074.console 2>&1
echo Dag074 OK
python "$G" python lean_guard.py logs/Dag075.log -o Dag075.olean Dag075.lean >logs/Dag075.console 2>&1
echo Dag075 OK
python "$G" python lean_guard.py logs/Dag076.log -o Dag076.olean Dag076.lean >logs/Dag076.console 2>&1
echo Dag076 OK
python "$G" python lean_guard.py logs/Dag077.log -o Dag077.olean Dag077.lean >logs/Dag077.console 2>&1
echo Dag077 OK
python "$G" python lean_guard.py logs/Dag078.log -o Dag078.olean Dag078.lean >logs/Dag078.console 2>&1
echo Dag078 OK
python "$G" python lean_guard.py logs/Dag079.log -o Dag079.olean Dag079.lean >logs/Dag079.console 2>&1
echo Dag079 OK
python "$G" python lean_guard.py logs/Dag080.log -o Dag080.olean Dag080.lean >logs/Dag080.console 2>&1
echo Dag080 OK
python "$G" python lean_guard.py logs/Dag081.log -o Dag081.olean Dag081.lean >logs/Dag081.console 2>&1
echo Dag081 OK
python "$G" python lean_guard.py logs/Dag082.log -o Dag082.olean Dag082.lean >logs/Dag082.console 2>&1
echo Dag082 OK
python "$G" python lean_guard.py logs/generated.th_lemma_4.log -o generated/th_lemma_4.olean generated/th_lemma_4.lean >logs/generated.th_lemma_4.console 2>&1
echo generated.th_lemma_4 OK
python "$G" python lean_guard.py logs/Dag083.log -o Dag083.olean Dag083.lean >logs/Dag083.console 2>&1
echo Dag083 OK
python "$G" python lean_guard.py logs/Dag084.log -o Dag084.olean Dag084.lean >logs/Dag084.console 2>&1
echo Dag084 OK
python "$G" python lean_guard.py logs/Dag085.log -o Dag085.olean Dag085.lean >logs/Dag085.console 2>&1
echo Dag085 OK
python "$G" python lean_guard.py logs/Dag086.log -o Dag086.olean Dag086.lean >logs/Dag086.console 2>&1
echo Dag086 OK
python "$G" python lean_guard.py logs/Dag087.log -o Dag087.olean Dag087.lean >logs/Dag087.console 2>&1
echo Dag087 OK
python "$G" python lean_guard.py logs/Dag088.log -o Dag088.olean Dag088.lean >logs/Dag088.console 2>&1
echo Dag088 OK
python "$G" python lean_guard.py logs/Dag089.log -o Dag089.olean Dag089.lean >logs/Dag089.console 2>&1
echo Dag089 OK
python "$G" python lean_guard.py logs/Dag090.log -o Dag090.olean Dag090.lean >logs/Dag090.console 2>&1
echo Dag090 OK
python "$G" python lean_guard.py logs/Dag091.log -o Dag091.olean Dag091.lean >logs/Dag091.console 2>&1
echo Dag091 OK
python "$G" python lean_guard.py logs/Dag092.log -o Dag092.olean Dag092.lean >logs/Dag092.console 2>&1
echo Dag092 OK
python "$G" python lean_guard.py logs/Dag093.log -o Dag093.olean Dag093.lean >logs/Dag093.console 2>&1
echo Dag093 OK
python "$G" python lean_guard.py logs/Dag094.log -o Dag094.olean Dag094.lean >logs/Dag094.console 2>&1
echo Dag094 OK
python "$G" python lean_guard.py logs/Dag095.log -o Dag095.olean Dag095.lean >logs/Dag095.console 2>&1
echo Dag095 OK
python "$G" python lean_guard.py logs/Dag096.log -o Dag096.olean Dag096.lean >logs/Dag096.console 2>&1
echo Dag096 OK
python "$G" python lean_guard.py logs/Dag097.log -o Dag097.olean Dag097.lean >logs/Dag097.console 2>&1
echo Dag097 OK
python "$G" python lean_guard.py logs/Dag098.log -o Dag098.olean Dag098.lean >logs/Dag098.console 2>&1
echo Dag098 OK
python "$G" python lean_guard.py logs/Dag099.log -o Dag099.olean Dag099.lean >logs/Dag099.console 2>&1
echo Dag099 OK
python "$G" python lean_guard.py logs/Dag100.log -o Dag100.olean Dag100.lean >logs/Dag100.console 2>&1
echo Dag100 OK
python "$G" python lean_guard.py logs/Dag101.log -o Dag101.olean Dag101.lean >logs/Dag101.console 2>&1
echo Dag101 OK
python "$G" python lean_guard.py logs/Dag102.log -o Dag102.olean Dag102.lean >logs/Dag102.console 2>&1
echo Dag102 OK
python "$G" python lean_guard.py logs/Dag103.log -o Dag103.olean Dag103.lean >logs/Dag103.console 2>&1
echo Dag103 OK
python "$G" python lean_guard.py logs/Dag104.log -o Dag104.olean Dag104.lean >logs/Dag104.console 2>&1
echo Dag104 OK
python "$G" python lean_guard.py logs/Dag105.log -o Dag105.olean Dag105.lean >logs/Dag105.console 2>&1
echo Dag105 OK
python "$G" python lean_guard.py logs/generated.th_lemma_5.log -o generated/th_lemma_5.olean generated/th_lemma_5.lean >logs/generated.th_lemma_5.console 2>&1
echo generated.th_lemma_5 OK
python "$G" python lean_guard.py logs/Dag106.log -o Dag106.olean Dag106.lean >logs/Dag106.console 2>&1
echo Dag106 OK
python "$G" python lean_guard.py logs/Dag107.log -o Dag107.olean Dag107.lean >logs/Dag107.console 2>&1
echo Dag107 OK
python "$G" python lean_guard.py logs/Dag108.log -o Dag108.olean Dag108.lean >logs/Dag108.console 2>&1
echo Dag108 OK
python "$G" python lean_guard.py logs/Dag109.log -o Dag109.olean Dag109.lean >logs/Dag109.console 2>&1
echo Dag109 OK
python "$G" python lean_guard.py logs/Dag110.log -o Dag110.olean Dag110.lean >logs/Dag110.console 2>&1
echo Dag110 OK
python "$G" python lean_guard.py logs/Dag111.log -o Dag111.olean Dag111.lean >logs/Dag111.console 2>&1
echo Dag111 OK
python "$G" python lean_guard.py logs/Dag112.log -o Dag112.olean Dag112.lean >logs/Dag112.console 2>&1
echo Dag112 OK
python "$G" python lean_guard.py logs/Dag113.log -o Dag113.olean Dag113.lean >logs/Dag113.console 2>&1
echo Dag113 OK
python "$G" python lean_guard.py logs/generated.th_lemma_6.log -o generated/th_lemma_6.olean generated/th_lemma_6.lean >logs/generated.th_lemma_6.console 2>&1
echo generated.th_lemma_6 OK
python "$G" python lean_guard.py logs/Dag114.log -o Dag114.olean Dag114.lean >logs/Dag114.console 2>&1
echo Dag114 OK
python "$G" python lean_guard.py logs/Dag115.log -o Dag115.olean Dag115.lean >logs/Dag115.console 2>&1
echo Dag115 OK
python "$G" python lean_guard.py logs/Dag116.log -o Dag116.olean Dag116.lean >logs/Dag116.console 2>&1
echo Dag116 OK
python "$G" python lean_guard.py logs/Dag117.log -o Dag117.olean Dag117.lean >logs/Dag117.console 2>&1
echo Dag117 OK
python "$G" python lean_guard.py logs/Dag118.log -o Dag118.olean Dag118.lean >logs/Dag118.console 2>&1
echo Dag118 OK
python "$G" python lean_guard.py logs/Dag119.log -o Dag119.olean Dag119.lean >logs/Dag119.console 2>&1
echo Dag119 OK
python "$G" python lean_guard.py logs/generated.th_lemma_7.log -o generated/th_lemma_7.olean generated/th_lemma_7.lean >logs/generated.th_lemma_7.console 2>&1
echo generated.th_lemma_7 OK
python "$G" python lean_guard.py logs/Dag120.log -o Dag120.olean Dag120.lean >logs/Dag120.console 2>&1
echo Dag120 OK
python "$G" python lean_guard.py logs/Dag121.log -o Dag121.olean Dag121.lean >logs/Dag121.console 2>&1
echo Dag121 OK
python "$G" python lean_guard.py logs/Dag122.log -o Dag122.olean Dag122.lean >logs/Dag122.console 2>&1
echo Dag122 OK
python "$G" python lean_guard.py logs/Dag123.log -o Dag123.olean Dag123.lean >logs/Dag123.console 2>&1
echo Dag123 OK
python "$G" python lean_guard.py logs/Dag124.log -o Dag124.olean Dag124.lean >logs/Dag124.console 2>&1
echo Dag124 OK
python "$G" python lean_guard.py logs/generated.th_lemma_8.log -o generated/th_lemma_8.olean generated/th_lemma_8.lean >logs/generated.th_lemma_8.console 2>&1
echo generated.th_lemma_8 OK
python "$G" python lean_guard.py logs/Dag125.log -o Dag125.olean Dag125.lean >logs/Dag125.console 2>&1
echo Dag125 OK
python "$G" python lean_guard.py logs/Dag126.log -o Dag126.olean Dag126.lean >logs/Dag126.console 2>&1
echo Dag126 OK
python "$G" python lean_guard.py logs/Dag127.log -o Dag127.olean Dag127.lean >logs/Dag127.console 2>&1
echo Dag127 OK
python "$G" python lean_guard.py logs/generated.th_lemma_9.log -o generated/th_lemma_9.olean generated/th_lemma_9.lean >logs/generated.th_lemma_9.console 2>&1
echo generated.th_lemma_9 OK
python "$G" python lean_guard.py logs/Dag128.log -o Dag128.olean Dag128.lean >logs/Dag128.console 2>&1
echo Dag128 OK
python "$G" python lean_guard.py logs/Dag129.log -o Dag129.olean Dag129.lean >logs/Dag129.console 2>&1
echo Dag129 OK
python "$G" python lean_guard.py logs/Dag130.log -o Dag130.olean Dag130.lean >logs/Dag130.console 2>&1
echo Dag130 OK
python "$G" python lean_guard.py logs/Dag131.log -o Dag131.olean Dag131.lean >logs/Dag131.console 2>&1
echo Dag131 OK
python "$G" python lean_guard.py logs/Dag132.log -o Dag132.olean Dag132.lean >logs/Dag132.console 2>&1
echo Dag132 OK
python "$G" python lean_guard.py logs/generated.th_lemma_10.log -o generated/th_lemma_10.olean generated/th_lemma_10.lean >logs/generated.th_lemma_10.console 2>&1
echo generated.th_lemma_10 OK
python "$G" python lean_guard.py logs/Dag133.log -o Dag133.olean Dag133.lean >logs/Dag133.console 2>&1
echo Dag133 OK
python "$G" python lean_guard.py logs/Dag134.log -o Dag134.olean Dag134.lean >logs/Dag134.console 2>&1
echo Dag134 OK
python "$G" python lean_guard.py logs/Dag135.log -o Dag135.olean Dag135.lean >logs/Dag135.console 2>&1
echo Dag135 OK
python "$G" python lean_guard.py logs/generated.th_lemma_11.log -o generated/th_lemma_11.olean generated/th_lemma_11.lean >logs/generated.th_lemma_11.console 2>&1
echo generated.th_lemma_11 OK
python "$G" python lean_guard.py logs/Dag136.log -o Dag136.olean Dag136.lean >logs/Dag136.console 2>&1
echo Dag136 OK
python "$G" python lean_guard.py logs/Dag137.log -o Dag137.olean Dag137.lean >logs/Dag137.console 2>&1
echo Dag137 OK
python "$G" python lean_guard.py logs/Dag138.log -o Dag138.olean Dag138.lean >logs/Dag138.console 2>&1
echo Dag138 OK
python "$G" python lean_guard.py logs/Dag139.log -o Dag139.olean Dag139.lean >logs/Dag139.console 2>&1
echo Dag139 OK
python "$G" python lean_guard.py logs/Dag140.log -o Dag140.olean Dag140.lean >logs/Dag140.console 2>&1
echo Dag140 OK
python "$G" python lean_guard.py logs/Dag141.log -o Dag141.olean Dag141.lean >logs/Dag141.console 2>&1
echo Dag141 OK
python "$G" python lean_guard.py logs/generated.th_lemma_12.log -o generated/th_lemma_12.olean generated/th_lemma_12.lean >logs/generated.th_lemma_12.console 2>&1
echo generated.th_lemma_12 OK
python "$G" python lean_guard.py logs/Dag142.log -o Dag142.olean Dag142.lean >logs/Dag142.console 2>&1
echo Dag142 OK
python "$G" python lean_guard.py logs/Dag143.log -o Dag143.olean Dag143.lean >logs/Dag143.console 2>&1
echo Dag143 OK
python "$G" python lean_guard.py logs/Dag144.log -o Dag144.olean Dag144.lean >logs/Dag144.console 2>&1
echo Dag144 OK
python "$G" python lean_guard.py logs/Dag145.log -o Dag145.olean Dag145.lean >logs/Dag145.console 2>&1
echo Dag145 OK
python "$G" python lean_guard.py logs/Dag146.log -o Dag146.olean Dag146.lean >logs/Dag146.console 2>&1
echo Dag146 OK
python "$G" python lean_guard.py logs/generated.th_lemma_13.log -o generated/th_lemma_13.olean generated/th_lemma_13.lean >logs/generated.th_lemma_13.console 2>&1
echo generated.th_lemma_13 OK
python "$G" python lean_guard.py logs/Dag147.log -o Dag147.olean Dag147.lean >logs/Dag147.console 2>&1
echo Dag147 OK
python "$G" python lean_guard.py logs/Dag148.log -o Dag148.olean Dag148.lean >logs/Dag148.console 2>&1
echo Dag148 OK
python "$G" python lean_guard.py logs/Dag149.log -o Dag149.olean Dag149.lean >logs/Dag149.console 2>&1
echo Dag149 OK
python "$G" python lean_guard.py logs/Dag150.log -o Dag150.olean Dag150.lean >logs/Dag150.console 2>&1
echo Dag150 OK
python "$G" python lean_guard.py logs/Dag151.log -o Dag151.olean Dag151.lean >logs/Dag151.console 2>&1
echo Dag151 OK
python "$G" python lean_guard.py logs/generated.th_lemma_14.log -o generated/th_lemma_14.olean generated/th_lemma_14.lean >logs/generated.th_lemma_14.console 2>&1
echo generated.th_lemma_14 OK
python "$G" python lean_guard.py logs/Dag152.log -o Dag152.olean Dag152.lean >logs/Dag152.console 2>&1
echo Dag152 OK
python "$G" python lean_guard.py logs/Dag153.log -o Dag153.olean Dag153.lean >logs/Dag153.console 2>&1
echo Dag153 OK
python "$G" python lean_guard.py logs/Dag154.log -o Dag154.olean Dag154.lean >logs/Dag154.console 2>&1
echo Dag154 OK
python "$G" python lean_guard.py logs/Dag155.log -o Dag155.olean Dag155.lean >logs/Dag155.console 2>&1
echo Dag155 OK
python "$G" python lean_guard.py logs/Dag156.log -o Dag156.olean Dag156.lean >logs/Dag156.console 2>&1
echo Dag156 OK
python "$G" python lean_guard.py logs/Dag157.log -o Dag157.olean Dag157.lean >logs/Dag157.console 2>&1
echo Dag157 OK
python "$G" python lean_guard.py logs/Dag158.log -o Dag158.olean Dag158.lean >logs/Dag158.console 2>&1
echo Dag158 OK
python "$G" python lean_guard.py logs/Dag159.log -o Dag159.olean Dag159.lean >logs/Dag159.console 2>&1
echo Dag159 OK
python "$G" python lean_guard.py logs/Dag160.log -o Dag160.olean Dag160.lean >logs/Dag160.console 2>&1
echo Dag160 OK
python "$G" python lean_guard.py logs/generated.th_lemma_15.log -o generated/th_lemma_15.olean generated/th_lemma_15.lean >logs/generated.th_lemma_15.console 2>&1
echo generated.th_lemma_15 OK
python "$G" python lean_guard.py logs/Dag161.log -o Dag161.olean Dag161.lean >logs/Dag161.console 2>&1
echo Dag161 OK
python "$G" python lean_guard.py logs/Dag162.log -o Dag162.olean Dag162.lean >logs/Dag162.console 2>&1
echo Dag162 OK
python "$G" python lean_guard.py logs/Dag163.log -o Dag163.olean Dag163.lean >logs/Dag163.console 2>&1
echo Dag163 OK
python "$G" python lean_guard.py logs/Dag164.log -o Dag164.olean Dag164.lean >logs/Dag164.console 2>&1
echo Dag164 OK
python "$G" python lean_guard.py logs/Dag165.log -o Dag165.olean Dag165.lean >logs/Dag165.console 2>&1
echo Dag165 OK
python "$G" python lean_guard.py logs/Dag166.log -o Dag166.olean Dag166.lean >logs/Dag166.console 2>&1
echo Dag166 OK
python "$G" python lean_guard.py logs/generated.th_lemma_16.log -o generated/th_lemma_16.olean generated/th_lemma_16.lean >logs/generated.th_lemma_16.console 2>&1
echo generated.th_lemma_16 OK
python "$G" python lean_guard.py logs/Dag167.log -o Dag167.olean Dag167.lean >logs/Dag167.console 2>&1
echo Dag167 OK
python "$G" python lean_guard.py logs/parts.Dag168_000.log -o parts/Dag168_000.olean parts/Dag168_000.lean >logs/parts.Dag168_000.console 2>&1
echo parts.Dag168_000 OK
python "$G" python lean_guard.py logs/parts.Dag168_001.log -o parts/Dag168_001.olean parts/Dag168_001.lean >logs/parts.Dag168_001.console 2>&1
echo parts.Dag168_001 OK
python "$G" python lean_guard.py logs/parts.Dag168_002.log -o parts/Dag168_002.olean parts/Dag168_002.lean >logs/parts.Dag168_002.console 2>&1
echo parts.Dag168_002 OK
python "$G" python lean_guard.py logs/parts.Dag168_003.log -o parts/Dag168_003.olean parts/Dag168_003.lean >logs/parts.Dag168_003.console 2>&1
echo parts.Dag168_003 OK
python "$G" python lean_guard.py logs/parts.Dag168_004.log -o parts/Dag168_004.olean parts/Dag168_004.lean >logs/parts.Dag168_004.console 2>&1
echo parts.Dag168_004 OK
python "$G" python lean_guard.py logs/parts.Dag168_005.log -o parts/Dag168_005.olean parts/Dag168_005.lean >logs/parts.Dag168_005.console 2>&1
echo parts.Dag168_005 OK
python "$G" python lean_guard.py logs/parts.Dag168_006.log -o parts/Dag168_006.olean parts/Dag168_006.lean >logs/parts.Dag168_006.console 2>&1
echo parts.Dag168_006 OK
python "$G" python lean_guard.py logs/parts.Dag168_007.log -o parts/Dag168_007.olean parts/Dag168_007.lean >logs/parts.Dag168_007.console 2>&1
echo parts.Dag168_007 OK
python "$G" python lean_guard.py logs/parts.Dag168_008.log -o parts/Dag168_008.olean parts/Dag168_008.lean >logs/parts.Dag168_008.console 2>&1
echo parts.Dag168_008 OK
python "$G" python lean_guard.py logs/parts.Dag168_009.log -o parts/Dag168_009.olean parts/Dag168_009.lean >logs/parts.Dag168_009.console 2>&1
echo parts.Dag168_009 OK
python "$G" python lean_guard.py logs/parts.Dag168_010.log -o parts/Dag168_010.olean parts/Dag168_010.lean >logs/parts.Dag168_010.console 2>&1
echo parts.Dag168_010 OK
python "$G" python lean_guard.py logs/parts.Dag168_011.log -o parts/Dag168_011.olean parts/Dag168_011.lean >logs/parts.Dag168_011.console 2>&1
echo parts.Dag168_011 OK
python "$G" python lean_guard.py logs/parts.Dag168_012.log -o parts/Dag168_012.olean parts/Dag168_012.lean >logs/parts.Dag168_012.console 2>&1
echo parts.Dag168_012 OK
python "$G" python lean_guard.py logs/parts.Dag168_013.log -o parts/Dag168_013.olean parts/Dag168_013.lean >logs/parts.Dag168_013.console 2>&1
echo parts.Dag168_013 OK
python "$G" python lean_guard.py logs/parts.Dag168_014.log -o parts/Dag168_014.olean parts/Dag168_014.lean >logs/parts.Dag168_014.console 2>&1
echo parts.Dag168_014 OK
python "$G" python lean_guard.py logs/parts.Dag168_015.log -o parts/Dag168_015.olean parts/Dag168_015.lean >logs/parts.Dag168_015.console 2>&1
echo parts.Dag168_015 OK
python "$G" python lean_guard.py logs/parts.Dag168_016.log -o parts/Dag168_016.olean parts/Dag168_016.lean >logs/parts.Dag168_016.console 2>&1
echo parts.Dag168_016 OK
python "$G" python lean_guard.py logs/parts.Dag168_017.log -o parts/Dag168_017.olean parts/Dag168_017.lean >logs/parts.Dag168_017.console 2>&1
echo parts.Dag168_017 OK
python "$G" python lean_guard.py logs/parts.Dag168_018.log -o parts/Dag168_018.olean parts/Dag168_018.lean >logs/parts.Dag168_018.console 2>&1
echo parts.Dag168_018 OK
python "$G" python lean_guard.py logs/parts.Dag168_019.log -o parts/Dag168_019.olean parts/Dag168_019.lean >logs/parts.Dag168_019.console 2>&1
echo parts.Dag168_019 OK
python "$G" python lean_guard.py logs/parts.Dag168_020.log -o parts/Dag168_020.olean parts/Dag168_020.lean >logs/parts.Dag168_020.console 2>&1
echo parts.Dag168_020 OK
python "$G" python lean_guard.py logs/parts.Dag168_021.log -o parts/Dag168_021.olean parts/Dag168_021.lean >logs/parts.Dag168_021.console 2>&1
echo parts.Dag168_021 OK
python "$G" python lean_guard.py logs/parts.Dag168_022.log -o parts/Dag168_022.olean parts/Dag168_022.lean >logs/parts.Dag168_022.console 2>&1
echo parts.Dag168_022 OK
python "$G" python lean_guard.py logs/parts.Dag168_023.log -o parts/Dag168_023.olean parts/Dag168_023.lean >logs/parts.Dag168_023.console 2>&1
echo parts.Dag168_023 OK
python "$G" python lean_guard.py logs/parts.Dag168_024.log -o parts/Dag168_024.olean parts/Dag168_024.lean >logs/parts.Dag168_024.console 2>&1
echo parts.Dag168_024 OK
python "$G" python lean_guard.py logs/parts.Dag168_025.log -o parts/Dag168_025.olean parts/Dag168_025.lean >logs/parts.Dag168_025.console 2>&1
echo parts.Dag168_025 OK
python "$G" python lean_guard.py logs/parts.Dag168_026.log -o parts/Dag168_026.olean parts/Dag168_026.lean >logs/parts.Dag168_026.console 2>&1
echo parts.Dag168_026 OK
python "$G" python lean_guard.py logs/parts.Dag168_027.log -o parts/Dag168_027.olean parts/Dag168_027.lean >logs/parts.Dag168_027.console 2>&1
echo parts.Dag168_027 OK
python "$G" python lean_guard.py logs/parts.Dag168_028.log -o parts/Dag168_028.olean parts/Dag168_028.lean >logs/parts.Dag168_028.console 2>&1
echo parts.Dag168_028 OK
python "$G" python lean_guard.py logs/parts.Dag168_029.log -o parts/Dag168_029.olean parts/Dag168_029.lean >logs/parts.Dag168_029.console 2>&1
echo parts.Dag168_029 OK
python "$G" python lean_guard.py logs/parts.Dag168_030.log -o parts/Dag168_030.olean parts/Dag168_030.lean >logs/parts.Dag168_030.console 2>&1
echo parts.Dag168_030 OK
python "$G" python lean_guard.py logs/parts.Dag168_031.log -o parts/Dag168_031.olean parts/Dag168_031.lean >logs/parts.Dag168_031.console 2>&1
echo parts.Dag168_031 OK
python "$G" python lean_guard.py logs/parts.Dag168_032.log -o parts/Dag168_032.olean parts/Dag168_032.lean >logs/parts.Dag168_032.console 2>&1
echo parts.Dag168_032 OK
python "$G" python lean_guard.py logs/parts.Dag168_033.log -o parts/Dag168_033.olean parts/Dag168_033.lean >logs/parts.Dag168_033.console 2>&1
echo parts.Dag168_033 OK
python "$G" python lean_guard.py logs/parts.Dag168_034.log -o parts/Dag168_034.olean parts/Dag168_034.lean >logs/parts.Dag168_034.console 2>&1
echo parts.Dag168_034 OK
python "$G" python lean_guard.py logs/parts.Dag168_035.log -o parts/Dag168_035.olean parts/Dag168_035.lean >logs/parts.Dag168_035.console 2>&1
echo parts.Dag168_035 OK
python "$G" python lean_guard.py logs/parts.Dag168_036.log -o parts/Dag168_036.olean parts/Dag168_036.lean >logs/parts.Dag168_036.console 2>&1
echo parts.Dag168_036 OK
python "$G" python lean_guard.py logs/parts.Dag168_037.log -o parts/Dag168_037.olean parts/Dag168_037.lean >logs/parts.Dag168_037.console 2>&1
echo parts.Dag168_037 OK
python "$G" python lean_guard.py logs/parts.Dag168_038.log -o parts/Dag168_038.olean parts/Dag168_038.lean >logs/parts.Dag168_038.console 2>&1
echo parts.Dag168_038 OK
python "$G" python lean_guard.py logs/parts.Dag168_039.log -o parts/Dag168_039.olean parts/Dag168_039.lean >logs/parts.Dag168_039.console 2>&1
echo parts.Dag168_039 OK
python "$G" python lean_guard.py logs/parts.Dag168_040.log -o parts/Dag168_040.olean parts/Dag168_040.lean >logs/parts.Dag168_040.console 2>&1
echo parts.Dag168_040 OK
python "$G" python lean_guard.py logs/parts.Dag168_041.log -o parts/Dag168_041.olean parts/Dag168_041.lean >logs/parts.Dag168_041.console 2>&1
echo parts.Dag168_041 OK
python "$G" python lean_guard.py logs/parts.Dag168_042.log -o parts/Dag168_042.olean parts/Dag168_042.lean >logs/parts.Dag168_042.console 2>&1
echo parts.Dag168_042 OK
python "$G" python lean_guard.py logs/parts.Dag168_043.log -o parts/Dag168_043.olean parts/Dag168_043.lean >logs/parts.Dag168_043.console 2>&1
echo parts.Dag168_043 OK
python "$G" python lean_guard.py logs/parts.Dag168_044.log -o parts/Dag168_044.olean parts/Dag168_044.lean >logs/parts.Dag168_044.console 2>&1
echo parts.Dag168_044 OK
python "$G" python lean_guard.py logs/Dag168.log -o Dag168.olean Dag168.lean >logs/Dag168.console 2>&1
echo Dag168 OK
python "$G" python lean_guard.py logs/Dag169.log -o Dag169.olean Dag169.lean >logs/Dag169.console 2>&1
echo Dag169 OK
python "$G" python lean_guard.py logs/Dag170.log -o Dag170.olean Dag170.lean >logs/Dag170.console 2>&1
echo Dag170 OK
python "$G" python lean_guard.py logs/Dag171.log -o Dag171.olean Dag171.lean >logs/Dag171.console 2>&1
echo Dag171 OK
python "$G" python lean_guard.py logs/generated.th_lemma_17.log -o generated/th_lemma_17.olean generated/th_lemma_17.lean >logs/generated.th_lemma_17.console 2>&1
echo generated.th_lemma_17 OK
python "$G" python lean_guard.py logs/Dag172.log -o Dag172.olean Dag172.lean >logs/Dag172.console 2>&1
echo Dag172 OK
python "$G" python lean_guard.py logs/Dag173.log -o Dag173.olean Dag173.lean >logs/Dag173.console 2>&1
echo Dag173 OK
python "$G" python lean_guard.py logs/Dag174.log -o Dag174.olean Dag174.lean >logs/Dag174.console 2>&1
echo Dag174 OK
python "$G" python lean_guard.py logs/Dag175.log -o Dag175.olean Dag175.lean >logs/Dag175.console 2>&1
echo Dag175 OK
python "$G" python lean_guard.py logs/generated.th_lemma_18.log -o generated/th_lemma_18.olean generated/th_lemma_18.lean >logs/generated.th_lemma_18.console 2>&1
echo generated.th_lemma_18 OK
python "$G" python lean_guard.py logs/Dag176.log -o Dag176.olean Dag176.lean >logs/Dag176.console 2>&1
echo Dag176 OK
python "$G" python lean_guard.py logs/Dag177.log -o Dag177.olean Dag177.lean >logs/Dag177.console 2>&1
echo Dag177 OK
python "$G" python lean_guard.py logs/Dag178.log -o Dag178.olean Dag178.lean >logs/Dag178.console 2>&1
echo Dag178 OK
python "$G" python lean_guard.py logs/generated.th_lemma_19.log -o generated/th_lemma_19.olean generated/th_lemma_19.lean >logs/generated.th_lemma_19.console 2>&1
echo generated.th_lemma_19 OK
python "$G" python lean_guard.py logs/Dag179.log -o Dag179.olean Dag179.lean >logs/Dag179.console 2>&1
echo Dag179 OK
python "$G" python lean_guard.py logs/Dag180.log -o Dag180.olean Dag180.lean >logs/Dag180.console 2>&1
echo Dag180 OK
python "$G" python lean_guard.py logs/Dag181.log -o Dag181.olean Dag181.lean >logs/Dag181.console 2>&1
echo Dag181 OK
python "$G" python lean_guard.py logs/generated.th_lemma_20.log -o generated/th_lemma_20.olean generated/th_lemma_20.lean >logs/generated.th_lemma_20.console 2>&1
echo generated.th_lemma_20 OK
python "$G" python lean_guard.py logs/Dag182.log -o Dag182.olean Dag182.lean >logs/Dag182.console 2>&1
echo Dag182 OK
python "$G" python lean_guard.py logs/Dag183.log -o Dag183.olean Dag183.lean >logs/Dag183.console 2>&1
echo Dag183 OK
python "$G" python lean_guard.py logs/Dag184.log -o Dag184.olean Dag184.lean >logs/Dag184.console 2>&1
echo Dag184 OK
python "$G" python lean_guard.py logs/Dag185.log -o Dag185.olean Dag185.lean >logs/Dag185.console 2>&1
echo Dag185 OK
python "$G" python lean_guard.py logs/Dag186.log -o Dag186.olean Dag186.lean >logs/Dag186.console 2>&1
echo Dag186 OK
python "$G" python lean_guard.py logs/generated.th_lemma_21.log -o generated/th_lemma_21.olean generated/th_lemma_21.lean >logs/generated.th_lemma_21.console 2>&1
echo generated.th_lemma_21 OK
python "$G" python lean_guard.py logs/Dag187.log -o Dag187.olean Dag187.lean >logs/Dag187.console 2>&1
echo Dag187 OK
python "$G" python lean_guard.py logs/Dag188.log -o Dag188.olean Dag188.lean >logs/Dag188.console 2>&1
echo Dag188 OK
python "$G" python lean_guard.py logs/Dag189.log -o Dag189.olean Dag189.lean >logs/Dag189.console 2>&1
echo Dag189 OK
python "$G" python lean_guard.py logs/Dag190.log -o Dag190.olean Dag190.lean >logs/Dag190.console 2>&1
echo Dag190 OK
python "$G" python lean_guard.py logs/Dag191.log -o Dag191.olean Dag191.lean >logs/Dag191.console 2>&1
echo Dag191 OK
python "$G" python lean_guard.py logs/generated.th_lemma_22.log -o generated/th_lemma_22.olean generated/th_lemma_22.lean >logs/generated.th_lemma_22.console 2>&1
echo generated.th_lemma_22 OK
python "$G" python lean_guard.py logs/Dag192.log -o Dag192.olean Dag192.lean >logs/Dag192.console 2>&1
echo Dag192 OK
python "$G" python lean_guard.py logs/Dag193.log -o Dag193.olean Dag193.lean >logs/Dag193.console 2>&1
echo Dag193 OK
python "$G" python lean_guard.py logs/Dag194.log -o Dag194.olean Dag194.lean >logs/Dag194.console 2>&1
echo Dag194 OK
python "$G" python lean_guard.py logs/Dag195.log -o Dag195.olean Dag195.lean >logs/Dag195.console 2>&1
echo Dag195 OK
python "$G" python lean_guard.py logs/Dag196.log -o Dag196.olean Dag196.lean >logs/Dag196.console 2>&1
echo Dag196 OK
python "$G" python lean_guard.py logs/generated.th_lemma_23.log -o generated/th_lemma_23.olean generated/th_lemma_23.lean >logs/generated.th_lemma_23.console 2>&1
echo generated.th_lemma_23 OK
python "$G" python lean_guard.py logs/Dag197.log -o Dag197.olean Dag197.lean >logs/Dag197.console 2>&1
echo Dag197 OK
python "$G" python lean_guard.py logs/Dag198.log -o Dag198.olean Dag198.lean >logs/Dag198.console 2>&1
echo Dag198 OK
python "$G" python lean_guard.py logs/Dag199.log -o Dag199.olean Dag199.lean >logs/Dag199.console 2>&1
echo Dag199 OK
python "$G" python lean_guard.py logs/Dag200.log -o Dag200.olean Dag200.lean >logs/Dag200.console 2>&1
echo Dag200 OK
python "$G" python lean_guard.py logs/generated.th_lemma_24.log -o generated/th_lemma_24.olean generated/th_lemma_24.lean >logs/generated.th_lemma_24.console 2>&1
echo generated.th_lemma_24 OK
python "$G" python lean_guard.py logs/Dag201.log -o Dag201.olean Dag201.lean >logs/Dag201.console 2>&1
echo Dag201 OK
python "$G" python lean_guard.py logs/Dag202.log -o Dag202.olean Dag202.lean >logs/Dag202.console 2>&1
echo Dag202 OK
python "$G" python lean_guard.py logs/Dag203.log -o Dag203.olean Dag203.lean >logs/Dag203.console 2>&1
echo Dag203 OK
python "$G" python lean_guard.py logs/Dag204.log -o Dag204.olean Dag204.lean >logs/Dag204.console 2>&1
echo Dag204 OK
python "$G" python lean_guard.py logs/generated.th_lemma_25.log -o generated/th_lemma_25.olean generated/th_lemma_25.lean >logs/generated.th_lemma_25.console 2>&1
echo generated.th_lemma_25 OK
python "$G" python lean_guard.py logs/Dag205.log -o Dag205.olean Dag205.lean >logs/Dag205.console 2>&1
echo Dag205 OK
python "$G" python lean_guard.py logs/Dag206.log -o Dag206.olean Dag206.lean >logs/Dag206.console 2>&1
echo Dag206 OK
python "$G" python lean_guard.py logs/Dag207.log -o Dag207.olean Dag207.lean >logs/Dag207.console 2>&1
echo Dag207 OK
python "$G" python lean_guard.py logs/Dag208.log -o Dag208.olean Dag208.lean >logs/Dag208.console 2>&1
echo Dag208 OK
python "$G" python lean_guard.py logs/Dag209.log -o Dag209.olean Dag209.lean >logs/Dag209.console 2>&1
echo Dag209 OK
python "$G" python lean_guard.py logs/generated.th_lemma_26.log -o generated/th_lemma_26.olean generated/th_lemma_26.lean >logs/generated.th_lemma_26.console 2>&1
echo generated.th_lemma_26 OK
python "$G" python lean_guard.py logs/Dag210.log -o Dag210.olean Dag210.lean >logs/Dag210.console 2>&1
echo Dag210 OK
python "$G" python lean_guard.py logs/Dag211.log -o Dag211.olean Dag211.lean >logs/Dag211.console 2>&1
echo Dag211 OK
python "$G" python lean_guard.py logs/Dag212.log -o Dag212.olean Dag212.lean >logs/Dag212.console 2>&1
echo Dag212 OK
python "$G" python lean_guard.py logs/Dag213.log -o Dag213.olean Dag213.lean >logs/Dag213.console 2>&1
echo Dag213 OK
python "$G" python lean_guard.py logs/Dag214.log -o Dag214.olean Dag214.lean >logs/Dag214.console 2>&1
echo Dag214 OK
python "$G" python lean_guard.py logs/generated.th_lemma_27.log -o generated/th_lemma_27.olean generated/th_lemma_27.lean >logs/generated.th_lemma_27.console 2>&1
echo generated.th_lemma_27 OK
python "$G" python lean_guard.py logs/Dag215.log -o Dag215.olean Dag215.lean >logs/Dag215.console 2>&1
echo Dag215 OK
python "$G" python lean_guard.py logs/Dag216.log -o Dag216.olean Dag216.lean >logs/Dag216.console 2>&1
echo Dag216 OK
python "$G" python lean_guard.py logs/Dag217.log -o Dag217.olean Dag217.lean >logs/Dag217.console 2>&1
echo Dag217 OK
python "$G" python lean_guard.py logs/Dag218.log -o Dag218.olean Dag218.lean >logs/Dag218.console 2>&1
echo Dag218 OK
python "$G" python lean_guard.py logs/Dag219.log -o Dag219.olean Dag219.lean >logs/Dag219.console 2>&1
echo Dag219 OK
python "$G" python lean_guard.py logs/generated.th_lemma_28.log -o generated/th_lemma_28.olean generated/th_lemma_28.lean >logs/generated.th_lemma_28.console 2>&1
echo generated.th_lemma_28 OK
python "$G" python lean_guard.py logs/Dag220.log -o Dag220.olean Dag220.lean >logs/Dag220.console 2>&1
echo Dag220 OK
python "$G" python lean_guard.py logs/Dag221.log -o Dag221.olean Dag221.lean >logs/Dag221.console 2>&1
echo Dag221 OK
python "$G" python lean_guard.py logs/Dag222.log -o Dag222.olean Dag222.lean >logs/Dag222.console 2>&1
echo Dag222 OK
python "$G" python lean_guard.py logs/Dag223.log -o Dag223.olean Dag223.lean >logs/Dag223.console 2>&1
echo Dag223 OK
python "$G" python lean_guard.py logs/Dag224.log -o Dag224.olean Dag224.lean >logs/Dag224.console 2>&1
echo Dag224 OK
python "$G" python lean_guard.py logs/generated.th_lemma_29.log -o generated/th_lemma_29.olean generated/th_lemma_29.lean >logs/generated.th_lemma_29.console 2>&1
echo generated.th_lemma_29 OK
python "$G" python lean_guard.py logs/Dag225.log -o Dag225.olean Dag225.lean >logs/Dag225.console 2>&1
echo Dag225 OK
python "$G" python lean_guard.py logs/Dag226.log -o Dag226.olean Dag226.lean >logs/Dag226.console 2>&1
echo Dag226 OK
python "$G" python lean_guard.py logs/Dag227.log -o Dag227.olean Dag227.lean >logs/Dag227.console 2>&1
echo Dag227 OK
python "$G" python lean_guard.py logs/Dag228.log -o Dag228.olean Dag228.lean >logs/Dag228.console 2>&1
echo Dag228 OK
python "$G" python lean_guard.py logs/Dag229.log -o Dag229.olean Dag229.lean >logs/Dag229.console 2>&1
echo Dag229 OK
python "$G" python lean_guard.py logs/generated.th_lemma_30.log -o generated/th_lemma_30.olean generated/th_lemma_30.lean >logs/generated.th_lemma_30.console 2>&1
echo generated.th_lemma_30 OK
python "$G" python lean_guard.py logs/Dag230.log -o Dag230.olean Dag230.lean >logs/Dag230.console 2>&1
echo Dag230 OK
python "$G" python lean_guard.py logs/Dag231.log -o Dag231.olean Dag231.lean >logs/Dag231.console 2>&1
echo Dag231 OK
python "$G" python lean_guard.py logs/Dag232.log -o Dag232.olean Dag232.lean >logs/Dag232.console 2>&1
echo Dag232 OK
python "$G" python lean_guard.py logs/Dag233.log -o Dag233.olean Dag233.lean >logs/Dag233.console 2>&1
echo Dag233 OK
python "$G" python lean_guard.py logs/Dag234.log -o Dag234.olean Dag234.lean >logs/Dag234.console 2>&1
echo Dag234 OK
python "$G" python lean_guard.py logs/Dag235.log -o Dag235.olean Dag235.lean >logs/Dag235.console 2>&1
echo Dag235 OK
python "$G" python lean_guard.py logs/Dag236.log -o Dag236.olean Dag236.lean >logs/Dag236.console 2>&1
echo Dag236 OK
python "$G" python lean_guard.py logs/generated.th_lemma_31.log -o generated/th_lemma_31.olean generated/th_lemma_31.lean >logs/generated.th_lemma_31.console 2>&1
echo generated.th_lemma_31 OK
python "$G" python lean_guard.py logs/Dag237.log -o Dag237.olean Dag237.lean >logs/Dag237.console 2>&1
echo Dag237 OK
python "$G" python lean_guard.py logs/Dag238.log -o Dag238.olean Dag238.lean >logs/Dag238.console 2>&1
echo Dag238 OK
python "$G" python lean_guard.py logs/Dag239.log -o Dag239.olean Dag239.lean >logs/Dag239.console 2>&1
echo Dag239 OK
python "$G" python lean_guard.py logs/generated.th_lemma_32.log -o generated/th_lemma_32.olean generated/th_lemma_32.lean >logs/generated.th_lemma_32.console 2>&1
echo generated.th_lemma_32 OK
python "$G" python lean_guard.py logs/Dag240.log -o Dag240.olean Dag240.lean >logs/Dag240.console 2>&1
echo Dag240 OK
python "$G" python lean_guard.py logs/Dag241.log -o Dag241.olean Dag241.lean >logs/Dag241.console 2>&1
echo Dag241 OK
python "$G" python lean_guard.py logs/Dag242.log -o Dag242.olean Dag242.lean >logs/Dag242.console 2>&1
echo Dag242 OK
python "$G" python lean_guard.py logs/Dag243.log -o Dag243.olean Dag243.lean >logs/Dag243.console 2>&1
echo Dag243 OK
python "$G" python lean_guard.py logs/Dag244.log -o Dag244.olean Dag244.lean >logs/Dag244.console 2>&1
echo Dag244 OK
python "$G" python lean_guard.py logs/Dag245.log -o Dag245.olean Dag245.lean >logs/Dag245.console 2>&1
echo Dag245 OK
python "$G" python lean_guard.py logs/Dag246.log -o Dag246.olean Dag246.lean >logs/Dag246.console 2>&1
echo Dag246 OK
python "$G" python lean_guard.py logs/generated.th_lemma_33.log -o generated/th_lemma_33.olean generated/th_lemma_33.lean >logs/generated.th_lemma_33.console 2>&1
echo generated.th_lemma_33 OK
python "$G" python lean_guard.py logs/Dag247.log -o Dag247.olean Dag247.lean >logs/Dag247.console 2>&1
echo Dag247 OK
python "$G" python lean_guard.py logs/Dag248.log -o Dag248.olean Dag248.lean >logs/Dag248.console 2>&1
echo Dag248 OK
python "$G" python lean_guard.py logs/Dag249.log -o Dag249.olean Dag249.lean >logs/Dag249.console 2>&1
echo Dag249 OK
python "$G" python lean_guard.py logs/Dag250.log -o Dag250.olean Dag250.lean >logs/Dag250.console 2>&1
echo Dag250 OK
python "$G" python lean_guard.py logs/Dag251.log -o Dag251.olean Dag251.lean >logs/Dag251.console 2>&1
echo Dag251 OK
python "$G" python lean_guard.py logs/Dag252.log -o Dag252.olean Dag252.lean >logs/Dag252.console 2>&1
echo Dag252 OK
python "$G" python lean_guard.py logs/generated.th_lemma_34.log -o generated/th_lemma_34.olean generated/th_lemma_34.lean >logs/generated.th_lemma_34.console 2>&1
echo generated.th_lemma_34 OK
python "$G" python lean_guard.py logs/Dag253.log -o Dag253.olean Dag253.lean >logs/Dag253.console 2>&1
echo Dag253 OK
python "$G" python lean_guard.py logs/Dag254.log -o Dag254.olean Dag254.lean >logs/Dag254.console 2>&1
echo Dag254 OK
python "$G" python lean_guard.py logs/Dag255.log -o Dag255.olean Dag255.lean >logs/Dag255.console 2>&1
echo Dag255 OK
python "$G" python lean_guard.py logs/Dag256.log -o Dag256.olean Dag256.lean >logs/Dag256.console 2>&1
echo Dag256 OK
python "$G" python lean_guard.py logs/Dag257.log -o Dag257.olean Dag257.lean >logs/Dag257.console 2>&1
echo Dag257 OK
python "$G" python lean_guard.py logs/Dag258.log -o Dag258.olean Dag258.lean >logs/Dag258.console 2>&1
echo Dag258 OK
python "$G" python lean_guard.py logs/Dag259.log -o Dag259.olean Dag259.lean >logs/Dag259.console 2>&1
echo Dag259 OK
python "$G" python lean_guard.py logs/generated.th_lemma_35.log -o generated/th_lemma_35.olean generated/th_lemma_35.lean >logs/generated.th_lemma_35.console 2>&1
echo generated.th_lemma_35 OK
python "$G" python lean_guard.py logs/Dag260.log -o Dag260.olean Dag260.lean >logs/Dag260.console 2>&1
echo Dag260 OK
python "$G" python lean_guard.py logs/Dag261.log -o Dag261.olean Dag261.lean >logs/Dag261.console 2>&1
echo Dag261 OK
python "$G" python lean_guard.py logs/Dag262.log -o Dag262.olean Dag262.lean >logs/Dag262.console 2>&1
echo Dag262 OK
python "$G" python lean_guard.py logs/Dag263.log -o Dag263.olean Dag263.lean >logs/Dag263.console 2>&1
echo Dag263 OK
python "$G" python lean_guard.py logs/Dag264.log -o Dag264.olean Dag264.lean >logs/Dag264.console 2>&1
echo Dag264 OK
python "$G" python lean_guard.py logs/Dag265.log -o Dag265.olean Dag265.lean >logs/Dag265.console 2>&1
echo Dag265 OK
python "$G" python lean_guard.py logs/generated.th_lemma_36.log -o generated/th_lemma_36.olean generated/th_lemma_36.lean >logs/generated.th_lemma_36.console 2>&1
echo generated.th_lemma_36 OK
python "$G" python lean_guard.py logs/Dag266.log -o Dag266.olean Dag266.lean >logs/Dag266.console 2>&1
echo Dag266 OK
python "$G" python lean_guard.py logs/Dag267.log -o Dag267.olean Dag267.lean >logs/Dag267.console 2>&1
echo Dag267 OK
python "$G" python lean_guard.py logs/Dag268.log -o Dag268.olean Dag268.lean >logs/Dag268.console 2>&1
echo Dag268 OK
python "$G" python lean_guard.py logs/Dag269.log -o Dag269.olean Dag269.lean >logs/Dag269.console 2>&1
echo Dag269 OK
python "$G" python lean_guard.py logs/Dag270.log -o Dag270.olean Dag270.lean >logs/Dag270.console 2>&1
echo Dag270 OK
python "$G" python lean_guard.py logs/generated.th_lemma_37.log -o generated/th_lemma_37.olean generated/th_lemma_37.lean >logs/generated.th_lemma_37.console 2>&1
echo generated.th_lemma_37 OK
python "$G" python lean_guard.py logs/Dag271.log -o Dag271.olean Dag271.lean >logs/Dag271.console 2>&1
echo Dag271 OK
python "$G" python lean_guard.py logs/Dag272.log -o Dag272.olean Dag272.lean >logs/Dag272.console 2>&1
echo Dag272 OK
python "$G" python lean_guard.py logs/Dag273.log -o Dag273.olean Dag273.lean >logs/Dag273.console 2>&1
echo Dag273 OK
python "$G" python lean_guard.py logs/Dag274.log -o Dag274.olean Dag274.lean >logs/Dag274.console 2>&1
echo Dag274 OK
python "$G" python lean_guard.py logs/Dag275.log -o Dag275.olean Dag275.lean >logs/Dag275.console 2>&1
echo Dag275 OK
python "$G" python lean_guard.py logs/Dag276.log -o Dag276.olean Dag276.lean >logs/Dag276.console 2>&1
echo Dag276 OK
python "$G" python lean_guard.py logs/Expansion.log -o Expansion.olean Expansion.lean >logs/Expansion.console 2>&1
echo Expansion OK
python "$G" python lean_guard.py logs/Symmetry.log -o Symmetry.olean Symmetry.lean >logs/Symmetry.console 2>&1
echo Symmetry OK
python "$G" python lean_guard.py logs/SourceBridge.log -o SourceBridge.olean SourceBridge.lean >logs/SourceBridge.console 2>&1
echo SourceBridge OK
python "$G" python lean_guard.py logs/Endpoint.log -o Endpoint.olean Endpoint.lean >logs/Endpoint.console 2>&1
echo Endpoint OK
python "$G" python lean_guard.py logs/Source.log -o Source.olean Source.lean >logs/Source.console 2>&1
echo Source OK
python "$G" python lean_guard.py logs/Audit000.log -o Audit000.olean Audit000.lean >logs/Audit000.console 2>&1
echo Audit000 OK
python "$G" python lean_guard.py logs/Audit001.log -o Audit001.olean Audit001.lean >logs/Audit001.console 2>&1
echo Audit001 OK
python "$G" python lean_guard.py logs/Audit002.log -o Audit002.olean Audit002.lean >logs/Audit002.console 2>&1
echo Audit002 OK
python "$G" python lean_guard.py logs/Audit003.log -o Audit003.olean Audit003.lean >logs/Audit003.console 2>&1
echo Audit003 OK
python "$G" python lean_guard.py logs/Audit004.log -o Audit004.olean Audit004.lean >logs/Audit004.console 2>&1
echo Audit004 OK
python "$G" python lean_guard.py logs/Audit005.log -o Audit005.olean Audit005.lean >logs/Audit005.console 2>&1
echo Audit005 OK
python "$G" python lean_guard.py logs/Audit006.log -o Audit006.olean Audit006.lean >logs/Audit006.console 2>&1
echo Audit006 OK
python "$G" python lean_guard.py logs/Audit007.log -o Audit007.olean Audit007.lean >logs/Audit007.console 2>&1
echo Audit007 OK
python "$G" python lean_guard.py logs/Audit008.log -o Audit008.olean Audit008.lean >logs/Audit008.console 2>&1
echo Audit008 OK
python "$G" python lean_guard.py logs/Audit009.log -o Audit009.olean Audit009.lean >logs/Audit009.console 2>&1
echo Audit009 OK
python "$G" python lean_guard.py logs/Audit010.log -o Audit010.olean Audit010.lean >logs/Audit010.console 2>&1
echo Audit010 OK
python "$G" python lean_guard.py logs/Audit011.log -o Audit011.olean Audit011.lean >logs/Audit011.console 2>&1
echo Audit011 OK
python "$G" python lean_guard.py logs/Audit012.log -o Audit012.olean Audit012.lean >logs/Audit012.console 2>&1
echo Audit012 OK
python "$G" python lean_guard.py logs/Audit013.log -o Audit013.olean Audit013.lean >logs/Audit013.console 2>&1
echo Audit013 OK
python "$G" python lean_guard.py logs/Audit014.log -o Audit014.olean Audit014.lean >logs/Audit014.console 2>&1
echo Audit014 OK
python "$G" python lean_guard.py logs/Audit015.log -o Audit015.olean Audit015.lean >logs/Audit015.console 2>&1
echo Audit015 OK
python "$G" python lean_guard.py logs/Audit016.log -o Audit016.olean Audit016.lean >logs/Audit016.console 2>&1
echo Audit016 OK
python "$G" python lean_guard.py logs/Audit017.log -o Audit017.olean Audit017.lean >logs/Audit017.console 2>&1
echo Audit017 OK
python "$G" python lean_guard.py logs/Audit018.log -o Audit018.olean Audit018.lean >logs/Audit018.console 2>&1
echo Audit018 OK
python "$G" python lean_guard.py logs/Audit019.log -o Audit019.olean Audit019.lean >logs/Audit019.console 2>&1
echo Audit019 OK
python "$G" python lean_guard.py logs/Audit020.log -o Audit020.olean Audit020.lean >logs/Audit020.console 2>&1
echo Audit020 OK
python "$G" python lean_guard.py logs/Audit021.log -o Audit021.olean Audit021.lean >logs/Audit021.console 2>&1
echo Audit021 OK
