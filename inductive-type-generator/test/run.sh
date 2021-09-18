SOFTWARE=../scr/comp
#Teste un type simple
$SOFTWARE < bit.ml4 > bit.v ; coqc bit.v
#Teste la prise en compte des arguments d'un constructeur
$SOFTWARE < natural.ml4 > natural.v ; coqc natural.v
#Teste le bon traitement d'un type à un seul constructeur
$SOFTWARE < color.ml4 > color.v ; coqc color.v
#Teste un type générique
$SOFTWARE < stack.ml4 > stack.v ; coqc stack.v
#Teste la prise en compte des tuples
$SOFTWARE < tree.ml4 > tree.v ; coqc tree.v
#Teste la prise en compte des fonctions
$SOFTWARE < comparator.ml4 > comparator.v ; coqc comparator.v
#Teste la prise en compte des types avec dépendances
$SOFTWARE < dependancy.ml4 > dependancy.v ; coqc dependancy.v
#Supprime les fichiers générés par coqc
rm -f *.vo *.glob
