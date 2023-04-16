# TODO

## Général

Devrait-on passer sur dune pour un modèle de compilation plus efficace ?
Devrait-on même garder le même répertoire git pour le simulateur que pour cubicle ?

## Model

- Utiliser une structure de donnée non persistante

## Simulateur

- La trace devrait garder le nb_proc
- Pour avoir un simulateur qui lit une trace : 
		Set la trace
		Set modèle vide
		Se balader dans la trace
- Un appel a step si il existe des états après la ou on est devrait retourner vers ces états. Une fonction tierce "forget future" devrait exister pour supprimer les traces futures.

## Traces

Implémenter la fonction "save trace", qui est une fonction avec la même signature que le modèle 
(de façon a pouvoir être lu par les mêmes programme)
Mais qui n'itère que sur un modèle.

## Compilateur

- Il faudrait un paramètre -o pour spécifier le path
- Mettre le "max_float" dans Simulator.Utils plutôt que dans le cutils
- La plupart du code entre l'écriture des garde et des états unsafe semble aisément factorisable
- Mettre un message dans la console pour dire que la compilation s'est bien passé et ou retrouver le fichier

## Scenes 

- Refresh l'écran lors d'une mise en pause pour afficher le texte
- Vérifier état unsafe 
- Afficher numéro du step courant quelque part

Dans un monde idéal : 
- Avoir des flèches qui sont des courbes et plus des droites pour permettre plus de flexibilité
- Ordonner proprement les procs pour qu'on comprenne bien qui est le nouveau proc

- Pouvoir zoomer et dézoomer avec la caméra
- Menu d'aide en appuyant sur h

Problème actuellement : SI on fait un step forward en étant en pause, le simulateur n'affiche pas la pause

On devrait pouvoir tuer un proc comme dans cubicle 
-> Regarder algo résistants aux pannes 

Pouvoir déplacer transition et état dans l'espace
Buttons dans leurs propre classe

Faire ascenceur:
Nécéssite d'avoir des boutons, ...

- Camera speed
- Camera on/off .. With mouse/without...

Mettre les boutons dans une classe a part pour les inputs

## TESTER PETRI

- dekker_n
- Hierarchical snoop

