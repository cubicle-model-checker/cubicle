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
- Ajouter les unsafe au modèle : 
	Nécéssite de créer une fonction pour créer le modèle correctement plutôt que de le créer dans les transitions

## Scenes 

- Casser les librairies (particulièrement petri) en plusieurs librairie pour pouvoir les utiliser a des endroits différents
- Améliorer les boutons: Avoir des boutons permettant d'indiquer si un bouton est cliquable, 
si la souris est sur un bouton changer sa couleur, ...
-> Les boutons peuvent devenir complexe et on peut penser a l'ajout d'un module Button

- Refresh l'écran lors d'une mise en pause pour afficher le texte

Dans un monde idéal : 
- Avoir des flèches qui sont des courbes et plus des droites pour permettre plus de flexibilité
- Afficher si la simulation est en pause ainsi que le numéro du step courant
- Ordonner proprement les procs pour qu'on comprenne bien qui est le nouveau proc

- Pouvoir zoomer et dézoomer avec la caméra
- Menu d'aide en appuyant sur h

## TESTER PETRI

- dekker_n
- Hierarchical snoop
