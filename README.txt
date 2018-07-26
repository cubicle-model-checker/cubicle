

------------------ Utilisation des canaux sous Cubicle ------------------


***** Déclaration *****

La déclaration d'un canal se fait de la façon suivante :

chan ChanName[chanType] : chanMsgType

ChanName : nom du canal
chanType : type de canal (N,N ; N,1 ; 1,N ; 1,1 ; CAUSAL ; ASYNC)
chanMsgType : type des messages (int, real, bool, proc...)


***** Groupes de canaux ****

Par défaut, les canaux sont indépendants. On peut regrouper des
canaux de même type en ajoutant une déclaration de la forme :

group { ChanName1, ..., ChanNameN }


***** Spécification du processus 'principal' *****

Chaque transition doit préciser quel est le processus effectuant
les envois et réceptions de messages (processus 'principal').
Pour cela, un des paramètres de la transition doit être
spécifié entre [], de la façon suivante :

transition t ([p] q r ...)
...


***** Envoi sur un canal *****

L'envoi d'un message sur un canal est réalisé dans la partie
actions d'une transition, de la façon suivante :

ChanName'q!v

ChanName : nom du canal
q (facultatif) : le processus qui recevra le message
v : une valeur du même type que les messages du canal


***** Réception depuis un canal *****

La réception d'un message depuis un canal peut être réalisée
aussi bien dans la garde d'une transition qu'en partie droite
d'une affectation, de la façon suivante :

ChanName'q?

ChanName : nom du canal
q (facultatif) : le processus qui a envoyé le message



***** Exemple de transition *****

transition t ([p] q)
requires { Chan1'q? = True }  (* p reçoit le message True de q sur Chan1 *)
{
    X[p] := Chan2?;           (* p reçoit un message sur Chan2 *)
    Chan3'q!42;               (* p envoie le message 42 à q sur Chan3 *)
}


