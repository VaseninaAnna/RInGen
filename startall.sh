dotnet build -c Release RInGen.sln
env 'myz3=/home/columpio/Documents/z3-chccomp21/build/myz3' dotnet bin/Release/net5.0/RInGen.dll solve --timelimit 300 myz3 --tipToHorn /home/columpio/Desktop/testersfield/benchmarks/TIP
# env 'myz3=/home/columpio/Documents/relz3' dotnet bin/Release/net5.0/RInGen.dll solve --timelimit 60 myz3 --tipToHorn /home/columpio/Desktop/testersfield/benchmarks/TIP
# env 'vampire=/home/columpio/Documents/vampire' 'VeriMAP-iddt=/home/columpio/Documents/VeriMAP-iddt-linux_x86_64/VeriMAP-iddt' 'eld=/home/columpio/Documents/eldarica/eld' dotnet bin/Release/net5.0/RInGen.dll solve --timelimit 300 all /home/columpio/Desktop/testersfield/jayhorn-sv-comp/chcs
# env 'vampire=/home/columpio/Documents/vampire' 'VeriMAP-iddt=/home/columpio/Documents/VeriMAP-iddt-linux_x86_64/VeriMAP-iddt' 'eld=/home/columpio/Documents/eldarica/eld' dotnet bin/Release/net5.0/RInGen.dll transform --tipToHorn /home/columpio/Desktop/testersfield/benchmarks/TIP
# env 'vampire=/home/columpio/Documents/vampire' 'VeriMAP-iddt=/home/columpio/Documents/VeriMAP-iddt-linux_x86_64/VeriMAP-iddt' 'eld=/home/columpio/Documents/eldarica/eld' dotnet bin/Release/net5.0/RInGen.dll solve --tipToHorn --timelimit 300 myz3 /home/columpio/Desktop/testersfield/benchmarks/TIP