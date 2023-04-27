# TODO

## Model

- Utiliser une structure de donnée non persistante

## Simulateur

- La trace devrait garder le nb_proc

## Compilateur

- Mettre le "max_float" dans Simulator.Utils plutôt que dans le cutils
- La plupart du code entre l'écriture des garde et des états unsafe semble aisément factorisable

## Scenes 

Dans un monde idéal : 
- Avoir des flèches qui sont des courbes et plus des droites pour permettre plus de flexibilité
- Ordonner proprement les procs pour qu'on comprenne bien qui est le nouveau proc
- Pouvoir zoomer et dézoomer avec la caméra
- Menu d'aide en appuyant sur h

On devrait pouvoir tuer un proc : 
-> Regarder algo résistants aux pannes 

Pouvoir déplacer transition et état dans l'espace

- Camera speed
- Camera on/off .. With mouse/without...

Composition.ml : Grid_composition.
La grid_composition doit être retirée de la PetriLib pour être générécisée dans la scenelib.

Meilleure librairie : 
Mettre couleur des boutons dans une structure, pareil pour indicateur 
Idéallement même une shape dans leurs structure (Cercle, Rectangle, filled ?)
Inconvéniant : On a une dépendance a Graphics... sauf si on stocke la couleur par un triplet rgb ... 
-> La couleur semble faisable après reflexion

## TESTER PETRI

- Hierarchical snoop

## NOTES : 

Quand on met un tiret dans le nom d'une variable, l'ast retire le tiret apparament : Souhaitable ?
