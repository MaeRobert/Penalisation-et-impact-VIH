# -*- coding: UTF-8 -*-

# Importation des packages nécessaires.
import sys
import numpy as np
import random
import csv
import gc

# Constantes.
RAYON_RECHERCHE_PARTENAIRE = 5
ESSAIS_RECHERCHE_PARTENAIRE = 3
CHANGE_PARTENAIRE_MOIS = 5
OUBLI_POLICE_MOIS = 3
CRIMINALISATION = False
PENALISATION_CLIENTeS = True
LEGALISATION = False
PROBA_NON_PROTECTION_TARIFE_CRIMINALISATION = 0.2
PROBA_NON_PROTECTION_TARIFE_NON_CRIMINALISATION = 0.05
COEFF_RAYON_RECHERCHE_PROSTITUEe = 30
COEFF_PROBA_VIOL = 0.5
PROBA_CONTAMINATION_SANS_PROTECTION = 0.01
PROPORTION_INFECTEeeS_NON_traiteEs = 24000.0/66000000.0
PROPORTION_INFECTEeeS_traiteEs = 149000.0/66000000.0

PROBA_RACISEe = 0.15
PROBA_TRANSGENRE = 0.03
PROBA_RACISEe_PAUVRETE = 0.5*0.15/0.3 # Avec probas conditionnelles.
PROBA_TRANSGENRE_PAUVRETE = 0.16*0.03/0.4 # Avec probas conditionnelles.
PROBA_PROSTITUTION_TRANSGENRE = 0.19
PROBA_PROSTITUTION_TRANSGENRE_ET_RACISEe = 0.47
PROPORTION_CLIENTeS = 0.06
PROBA_USAGE_DROGUES_GRANDE_PRECARITE = 300000.0*(0.46*0.30+0.16*0.8)/(66000000.0*0.1)
PROBA_USAGE_DROGUES_PRECARITE = 300000.0*(0.46*0.50+0.16*0.23)/(66000000.0*0.4)
PROBA_USAGE_DROGUES = 300000.0*0.3/66000000.0
PROBA_TOUJOURS_PROTECTION_GRANDE_PRECARITE = 0.62
PROBA_SOUVENT_PROTECTION_GRANDE_PRECARITE = 0.25
PROBA_TOUJOURS_PROTECTION_MOYENNE_PRECARITE = 0.725
PROBA_SOUVENT_PROTECTION_MOYENNE_PRECARITE = 0.23
PROBA_TOUJOURS_PROTECTION_AUTRE_PRECARITE =0.85
PROBA_SOUVENT_PROTECTION_AUTRE_PRECARITE = 0.10


# Classe pour la gestion des contaminations au VIH.
class VIH:

    # Énumération des différents statuts possibles.
    NON_INFECTEe         = 0
    INFECTEe_NON_TRAITEe = 1
    INFECTEe_TRAITEe     = 2

    # Retourne la probabilité de s'INFECTEer lors d'un rapport.
    # Ce type de probabilité peut être implémenter sous forme d'une formule, d'une suite de conditions.
    # ("if"/"elif"/"else"), de tableau, etc. ou une combinaison de toutes ces possibilités.
    @staticmethod
    def probabilite_infection_rapport(humainE):
        if humainE.precarite > 0.8:
            return 51.0*267.0/66000000.0
        elif humainE.precarite > 0.6:
            return 31.7*267.0/66000000.0
        elif humainE.precarite > 0.4:
            return 10.5*267.0/66000000.0
        elif humainE.precarite > 0.2:
            return 6.7*267.0/66000000.0
        else:
            return 1.5*267.0/66000000.0

    # Retourne la probabilité de s'infecter lors d'une prise de drogue.
    @staticmethod
    def probabilite_infection_drogue(humainE):
        return 2300.0/66000000.0

    # Retourne la probabilité d'obtenir un traitement.
    @staticmethod
    def probabilite_traitement(humainE):
        if type(humainE) != prostitueE:
            return pow(1.0 - humainE.precarite, 3.0)/2
        else:
            if humainE.precarite > 0.95:
                return 0.9
            else:
                return 0.5





# Classe pour la gestion de la police.
class police:

    # Retourne la probabilité de se faire contrôler par la police.
    @staticmethod
    def probabilite_controle(humainE):
        if type(humainE) is clientE:
            if PENALISATION_CLIENTeS:
                return (humainE.usage_drogues + humainE.raciseE + humainE.precarite+2.0*humainE.activite) / 5.0
            else:
                return (humainE.usage_drogues + humainE.raciseE + humainE.precarite) / 5.0
        elif type(humainE) is prostitueE:
            if CRIMINALISATION:
                return (humainE.usage_drogues + humainE.raciseE + humainE.precarite+2.0) / 5.0
            else:
                return (humainE.usage_drogues + humainE.raciseE + humainE.precarite+1.0) / 5.0
        else:
            return (humainE.usage_drogues + humainE.raciseE + humainE.precarite) / 5.0







# Classe de base représentant un.e "humainE" (individu).
# Une ville est un tableau à 2 dimensions constitués d'humain.e.s.
# Chaque humain.e est un agent indépendant dont certaines caractéristiques sont mises à jour à chaque tour.
# Cette classe est dérivée en 2 sous-classes spécifiques : la classe "clientE" et la classe "prostitueE".
class humainE(object):

    # Variables de classe : décompte des infections traitées et non-traitées.
    nombre_total     = 0
    nombre_infecteEs = 0
    nombre_traiteEs  = 0

    # Crée un.e humain.e en spécifiant ses différentes caractéristiques.
    def __init__(self, ville, statut_vih, precarite, usage_drogues, raciseE, transgenre, abscisse, ordonnee):

        # Mémorise la ville à laquelle on appartient.
        self.ville = ville

        # Statut de cet individu en ce qui concerne le VIH.
        self.statut_vih = statut_vih

        # Caractéristiques de cet individu (valeurs toutes comprises entre 0.0 et 1.0).
        self.precarite         = precarite # 0.0 : les moins précaires.
        self.usage_drogues     = usage_drogues
        self.raciseE           = raciseE
        self.transgenre        = transgenre
        self.trauma_police     = 0.0 # Traumatisme subi suite à un contrôle de police.
        self.change_partenaire = 0.0 # Désir de changer de partenaire.

        # Coordonnées de l'individu dans la ville.
        self.abscisse = abscisse
        self.ordonnee = ordonnee

        # Pas de partenaire au départ...
        self.partenaire = None;

        # Un individu de plus...
        self.__class__.nombre_total += 1
        if self.statut_vih != VIH.NON_INFECTEe:
            self.__class__.nombre_infecteEs += 1
            if self.statut_vih == VIH.INFECTEe_TRAITEe:
                self.__class__.nombre_traiteEs += 1

        self.__class__.somme_precarite += self.precarite
        self.__class__.somme_etat_mental += self.etat_mental()

    # Retourne l'état mental de cet individu, de 0.0 (le meilleur) à 1.0 (le pire).
    def etat_mental(self):

        # Ici, l'implémentation est très approximative, mais permet de montrer l'influence de ces différents
        # facteurs sur l'état mental d'un individu. On pourra éventuellement définir des coefficient ou autres
        # formules.
        # Remarque : on divise par 8 car l'on rajoutera certains facteurs pour les prostitué.e.s, dont l'état mental
        # sera souvent empiré par la putophobie et leurs conditions de travail.
        return (self.precarite + self.usage_drogues + self.raciseE + self.transgenre + self.trauma_police) / 8.0

    # Choisit un.e partenaire pour cet individu. Note : il est possible de rester sans partenaire...
    def choix_partenaire(self, rayon_recherche, nombre_essais):

        # Vérifie si l'individu a déjà un.e partenaire et qu'il ne désire pas en changer.
        if self.partenaire is not None and self.change_partenaire < 1.0:

            # Modifie le désire de changement.
            self.change_partenaire = min (1.0, self.change_partenaire + 1.0 / CHANGE_PARTENAIRE_MOIS)

        else:

            # Prévient l'éventuel.le partenaire actuel.le de ce changement.
            if self.partenaire is not None:
                self.partenaire.partenaire = None
            self.partenaire = None

            # Cherche un.e partenaire à proximité.
            xmin = max(self.abscisse - rayon_recherche, 0)
            xmax = min(self.abscisse + rayon_recherche, self.ville.largeur - 1)
            ymin = max(self.ordonnee - rayon_recherche, 0)
            ymax = min(self.ordonnee + rayon_recherche, self.ville.hauteur - 1)

            for essai in range(nombre_essais):
                x = random.randint(xmin, xmax)
                y = random.randint(ymin, ymax)
                voisin = self.ville.humainEs[x][y]
                if voisin != self and voisin.partenaire is None:

                    # Un nouveau couple est formé.
                    self.partenaire = voisin
                    voisin.partenaire = self

                    # Ré-initialise le désire de changement des 2 partenaires.
                    self.change_partenaire = 0.0
                    voisin.change_partenaire = 0.0
                    break

    # Met à jour le statut vis à vis du VIH après un rapport non-tarifé.
    def infection_vih_rapport_non_tarife(self):

        # Rien ne se passe si l'individu n'a pas de partenaire.
        if self.partenaire is None:
            return

        # Un individu non-infecté peut le devenir si saon partenaire est infecté.e et non-traité.e.
        # Note : on ne s'occupe ici que de "self", le statut du/de la partenaire sera mis à jour par iel-même.
        if self.statut_vih == VIH.NON_INFECTEe and self.partenaire.statut_vih == VIH.INFECTEe_NON_TRAITEe:
            if random.random() < VIH.probabilite_infection_rapport(self):
                self.statut_vih = VIH.INFECTEe_NON_TRAITEe
                self.__class__.nombre_infecteEs += 1

    # Met à jour le statut vis à vis du VIH après une prise de drogue.
    def infection_vih_drogue(self):
        if self.statut_vih == VIH.NON_INFECTEe:
            if random.random() < VIH.probabilite_infection_drogue(self)* self.usage_drogues:
                self.statut_vih = VIH.INFECTEe_NON_TRAITEe
                self.__class__.nombre_infecteEs += 1

    # Met à jour le statut vis à vis du VIH après traitement.
    def traitement_vih(self):
        if self.statut_vih == VIH.INFECTEe_NON_TRAITEe:
            if random.random() < VIH.probabilite_traitement(self):
                self.statut_vih = VIH.INFECTEe_TRAITEe
                self.__class__.nombre_traiteEs += 1

    # Met à jour le controle de la police (1.0 = l'individu vient tout juste de se faire contrôler).
    def controle_police(self):

        # Est-ce que l'individu subit un contrôle de police ?
        if random.random() < police.probabilite_controle(self):

            # Un contrôle de police est fait.
            self.trauma_police = 1.0
        else:

            # Le traumatisme du contrôle est peu à peu oublié.
            self.trauma_police = max(0.0, self.trauma_police - 1.0 / OUBLI_POLICE_MOIS)

    # Met à jour l'individu ce tour-ci.
    def simule_un_mois(self):
        self.choix_partenaire(RAYON_RECHERCHE_PARTENAIRE, ESSAIS_RECHERCHE_PARTENAIRE)
        self.infection_vih_drogue()
        self.infection_vih_rapport_non_tarife()
        self.traitement_vih()
        self.controle_police()
        self.__class__.somme_precarite += self.precarite
        self.__class__.somme_etat_mental += self.etat_mental()

    # Suppression d'un individu (normalement non-utilisé, sauf si la ville est détruite)
    def __del__(self):

        # Un individu de moins...
        self.__class__.nombre_total -= 1
        if self.statut_vih != VIH.NON_INFECTEe:
            self.__class__.nombre_infecteEs -= 1
            if self.statut_vih == VIH.INFECTEe_TRAITEe:
                self.__class__.nombre_traiteEs -= 1





# Classe représentant un.e client.e.
class clientE(humainE):

    # Crée lae client.e en spécifiant ses différentes caractéristiques.
    def __init__(self, ville, statut_vih, precarite, usage_drogues, raciseE, transgenre, abscisse, ordonnee, dangerosite, coeff_rayon_recherche_prostitueE, proba_viol):
        super(clientE, self).__init__(ville, statut_vih, precarite, usage_drogues, raciseE, transgenre, abscisse, ordonnee)
        self.dangerosite = dangerosite
        self.compteur_inactivite = 0.0
        self.activite = 1.0 # Au debut au moins, actif.ve en tant que client.e.
        self.coeff_rayon_recherche_prostitueE = coeff_rayon_recherche_prostitueE
        self.proba_viol = proba_viol

    def determine_activite(self):
        police = self.trauma_police
        if police == 1.0:
            if self.dangerosite <= 0.0:
                self.compteur_inactivite = 1.0
            elif self.dangerosite <= 0.25:
                self.compteur_inactivite = 0.75
            else:
                self.compteur_inactivite = 0.0
        else:
            self.compteur_inactivite = max(self.compteur_inactivite-0.25,0.0)
        if self.compteur_inactivite <= 0.0:
            self.activite = 1.0
        else:
            self.activite = 0.0

    def choix_prostitueE(self):
        liste=[]

        # Prise en compte de la position géographique.
        if self.precarite >= 0.25:
            xmin = max(self.abscisse - (1.25-self.precarite)*self.coeff_rayon_recherche_prostitueE, 0)
            xmax = min(self.abscisse + (1.25-self.precarite)*self.coeff_rayon_recherche_prostitueE, self.ville.largeur - 1)
            ymin = max(self.ordonnee - (1.25-self.precarite)*self.coeff_rayon_recherche_prostitueE, 0)
            ymax = min(self.ordonnee + (1.25-self.precarite)*self.coeff_rayon_recherche_prostitueE, self.ville.hauteur - 1)
        else:
            xmin = 0
            xmax = self.ville.largeur - 1
            ymin = 0
            ymax = self.ville.hauteur - 1

        for prostitueE in (self.ville.liste_prostitueEs):
            if prostitueE.abscisse >= xmin and prostitueE.abscisse <= xmax and prostitueE.ordonnee >= ymin and prostitueE.ordonnee <= ymax:
                liste.append(prostitueE)
                # liste_prostitueEs est triée donc liste sera aussi triée dans l'ordre de la précarité.

        # Prise en compte de la précarité et de la dangerosité.
        # Moins lae client.e est précaire, moins iel ira vers des prositué.e.s précaires.
        # Mais en fonction de la dangerosité, cela peut changer.
        # Si liste==[], on ne renvoie rien (va juste agir par effet de bord sur prostitueE.clientEs).
        if liste != []:
            n = len(liste)
            if self.precarite > 0.75:
                choix = liste[random.randint(0,int(0.25*n))]
            elif self.precarite > 0.5:
                choix = liste[random.randint(0,int(0.5*n))]
            else:
                if self.dangerosite > 0.5:
                    choix = liste[random.randint(0, n - 1)]
                else:
                    choix = liste[random.randint(int(0.4*n), n - 1)]

            # On va insérer lae client.e au bon endroit dans choix.liste_clientEs,
            # qui sera triée par ordre de dangerosité.
            i = 0
            while i < len(choix.liste_clientEs) and choix.liste_clientEs[i][0].dangerosite < self.dangerosite:
                i += 1
            choix.liste_clientEs.insert(i,(self, 1.0))


    def choix_viol(self, prostitueE):
        diff_precarite = max(prostitueE.precarite - self.precarite,0)
        # La seule différence de précarité qui compte est celle où lae clientE est plus riche que lae prostitué.e
        # car iel est alors en position de domination ; alors que l'autre sens ne changera rien.

        # Ici on rajoute une courte boucle pour prendre en compte l'état mental de la personne prostituée,
        # que lae clientE peut considérer comme une forme de vulnérabilité.
        if prostitueE.etat_mental() >= 0.28:
            essai = 2
        else:
            essai = 1

        i = 0
        viol = False
        while i < essai and viol == False:
            if random.random() <= self.proba_viol and random.random() <= 0.5*prostitueE.garde_corps :
                prostitueE.agression = (prostitueE.agression+1.0)/2.0
                viol = True
            else:
                viol = False
            i+=1
        return viol
        # proba_viol est un tableau à double entrée donnant la "probabilité" d'un viol à la fois en fonction de la
        # dangerosité du/de la client.e, et de la différence de precarité entre iel et lae prostitué.e.
        # prostitueE.garde_du_corps = 0 ou 1 : on suppose (c'est un choix arbitraire et critiquable, mais l'idée est
        # plus de montrer le phénomène) que les risques de viol sont réduits de moitié avec un.e garde du corps...

    def simule_un_mois(self):
        super(clientE, self).simule_un_mois()
        self.determine_activite()
        if self.activite == 1.0:
            self.choix_prostitueE()




# Classe représentant une personne prostituée.
class prostitueE(humainE):

    # Créée la personne prostituée en spécifiant ses différentes caractéristiques.
    def __init__(self, ville, statut_vih, precarite, usage_drogues, raciseE, transgenre, abscisse, ordonnee, garde_corps,association, nombre_clientEs, tarifs):

        self.garde_corps = garde_corps
        self.association = association
        self.agression = 0.0 # On considère qu'au départ il n'y a eu aucune agression.
        self.liste_clientEs = [] # Liste des clientE.s potentiel.le.s qui est mise à jour lorsque les clientE.s
        # font leur choix, avec la fonction choix_prostitueE.
        self.nombre_clientEs = nombre_clientEs
        self.tarifs = tarifs
        super(prostitueE, self).__init__(ville, statut_vih, precarite, usage_drogues, raciseE, transgenre, abscisse, ordonnee)

    @staticmethod
    def calcul_precarite(x):
        return 1.00*(x-1000.0)*(x-2000.0)*(x-3000.0)*(x-5000.0)*(x-7000.0)/((-1000.0)*(-2000.0)*(-3000.0)*(-5000.0)*(-7000.0)) + 0.8*x*(x-2000.0)*(x-3000.0)*(x-5000.0)*(x-7000.0)/((1000.0)*(-1000.0)*(-2000.0)*(-4000.0)*(-6000.0)) + 0.6*x*(x-1000.0)*(x-3000.0)*(x-5000.0)*(x-7000.0)/((2000.0)*(1000.0)*(-1000.0)*(-3000.0)*(-5000.0)) + 0.4*x*(x-1000.0)*(x-2000.0)*(x-5000.0)*(x-7000.0)/((3000.0)*(2000.0)*(1000.0)*(-2000.0)*(-4000.0)) +  0.2*x*(x-1000.0)*(x-2000.0)*(x-3000.0)*(x-7000.0)/((5000.0)*(4000.0)*(3000.0)*(2000.0)*(-2000.0)) + 0.0

    def etat_mental(self):
        return super(prostitueE, self).etat_mental() + 3.0*self.agression/8.0


    def choix_clientE(self):
        if self.liste_clientEs != []:
            n = len(self.liste_clientEs)
            if self.association == 0.0:
                num = random.randint(0,n - 1)
            else:
                num = random.randint(0,int(2*n/3)) # Les associations et plus globalement l'entraide entre
                # travailleur.euse.s du sexe permettent de se transmettre les informations sur les client.e.s les plus
                # dangereu.x.ses, qui pourront alors éventuellement être évité.e.s.
            choix = self.liste_clientEs[num]
        else:
            choix = (None,0.0)
        return choix


    def determine_frequence_protection(self):
        alea = random.random()
        if self.precarite > 0.94:
            if alea < PROBA_TOUJOURS_PROTECTION_GRANDE_PRECARITE:
                return 0.95
            elif alea < PROBA_TOUJOURS_PROTECTION_GRANDE_PRECARITE + PROBA_SOUVENT_PROTECTION_GRANDE_PRECARITE:
                return 0.8
            else:
                return 0.5
        elif self.precarite > 0.89:
            if alea < PROBA_TOUJOURS_PROTECTION_MOYENNE_PRECARITE:
                return 1.0
            elif alea < PROBA_TOUJOURS_PROTECTION_MOYENNE_PRECARITE + PROBA_SOUVENT_PROTECTION_MOYENNE_PRECARITE:
                return 0.85
            else:
                return 0.6
        else:
            if alea < PROBA_TOUJOURS_PROTECTION_AUTRE_PRECARITE:
                return 1.0
            elif alea < PROBA_TOUJOURS_PROTECTION_AUTRE_PRECARITE + PROBA_SOUVENT_PROTECTION_AUTRE_PRECARITE:
                return 0.9
            else:
                return 0.7


    def ok_rapport_non_protege(self):
        # Dépend de la précarité, de l'usage de drogues, et de la peur de la police due aux contrôles fréquents si
        # criminalisation il y a (les préservatifs peuvent constituer des preuves de la prostitution de
        # la personne).
        ok_sans_protection = False
        if random.random() < (1 - self.determine_frequence_protection()):
            ok_sans_protection = True

        if ok_sans_protection == False:
            if CRIMINALISATION:
                for i in range(int(self.trauma_police*4)):
                    if random.random() < PROBA_NON_PROTECTION_TARIFE_CRIMINALISATION:
                        ok_sans_protection = True
                        break
                # Cette boucle permet de prendre en compte la peur induite par la police.
            else:
                for i in range(int(self.trauma_police*4)):
                    if random.random() < PROBA_NON_PROTECTION_TARIFE_NON_CRIMINALISATION:
                        ok_sans_protection = True
                        break

        return ok_sans_protection


    def rapports_tarifes(self):

        argent_gagne = 0.0
        i = 0
        while self.liste_clientEs != [] and i < self.nombre_clientEs:
            choix,temps_avant_oubli = self.choix_clientE()
            argent_gagne += self.tarifs
            self.liste_clientEs.remove((choix,temps_avant_oubli))

            if choix.choix_viol(self) or  self.ok_rapport_non_protege():
                if random.random() < PROBA_CONTAMINATION_SANS_PROTECTION:
                    if choix.statut_vih == VIH.INFECTEe_NON_TRAITEe and self.statut_vih == VIH.NON_INFECTEe:
                        self.statut_vih = VIH.INFECTEe_NON_TRAITEe
                        self.__class__.nombre_infecteEs += 1
                    elif self.statut_vih == VIH.INFECTEe_NON_TRAITEe and choix.statut_vih == VIH.NON_INFECTEe:
                        choix.statut_vih = VIH.INFECTEe_NON_TRAITEe
                        choix.__class__.nombre_infecteEs += 1

            i += 1

        if self.liste_clientEs != []:
            for i in range(len(self.liste_clientEs)):
                (clientE,temps_avant_oubli)=self.liste_clientEs[i]
                temps_avant_oubli -= 0.5
                if temps_avant_oubli <= 0.0:
                    del self.liste_clientEs[i]

        self.precarite = prostitueE.calcul_precarite(argent_gagne)


    def simule_un_mois(self):

        super(prostitueE, self).simule_un_mois()
        self.rapports_tarifes()




# Classe représentant la ville, un tableau à 2 dimensions constitué d'humain.e.s.
class ville:

    # Retourne la précarité d'un endroit de la ville.
    # La précarité, quoique légèrement aléatoire, dépend de la géographie de la ville.
    def determine_precarite(self, x, y):

        if x < self.largeur / 5:
            return random.uniform(0.5,0.2)
        elif x < 2*self.largeur / 5:
            if y < self.hauteur / 5 :
                return random.uniform(0.5,0.2)
            elif y < 4*self.hauteur / 5:
                return random.uniform(0.65,0.3)
            else:
                return random.uniform(0.5,0.2)
        elif x < 3*self.largeur / 5:
            if y < self.hauteur / 5 :
                return random.uniform(0.8,0.5)
            elif y < 2*self.hauteur / 5:
                return random.uniform(0.65,0.3)
            elif y < 3*self.hauteur / 5:
                return random.uniform(0.4,0.1)
            elif y < 4*self.hauteur / 5:
                return random.uniform(0.65,0.3)
            else:
                return random.uniform(0.5,0.2)
        elif x < 4*self.largeur / 5:
            if y < self.hauteur / 5 :
                return random.uniform(0.8,0.5)
            elif y < 2*self.hauteur / 5:
                return random.uniform(1.0,0.8)
            elif y < 3*self.hauteur / 5:
                return random.uniform(0.65,0.3)
            elif y < 4*self.hauteur / 5:
                return random.uniform(1.0,0.8)
            else:
                return random.uniform(0.8,0.5)
        else:
            return random.uniform(0.8,0.5)


    @staticmethod
    def determine_usage_drogues(precarite):
        alea = random.random()
        if precarite >= 0.98:
            if alea < PROBA_USAGE_DROGUES_GRANDE_PRECARITE:
                return 1.0
            else:
                return 0.0
        elif precarite >= 0.8:
            if alea < PROBA_USAGE_DROGUES_PRECARITE:
                return 1.0
            else:
                return 0.0
        else:
            if alea < PROBA_USAGE_DROGUES:
                return 1.0
            else:
                return 0.0

    @staticmethod
    def determine_raciseE(precarite):
        alea = random.random()
        if precarite < 0.3:
            if alea < PROBA_RACISEe_PAUVRETE:
                return 1.0
            else:
                return 0.0
        else:
            if alea < PROBA_RACISEe:
                return 1.0
            else:
                return 0.0

    @staticmethod
    def determine_transgenre(precarite):
        alea = random.random()
        if precarite < 0.4:
            if alea < PROBA_TRANSGENRE_PAUVRETE:
                return 1.0
            else:
                return 0.0
        else:
            if alea < PROBA_TRANSGENRE:
                return 1.0
            else:
                return 0.0

    @staticmethod
    def proba_prostitution(precarite, transgenre, raciseE):
        if transgenre == 1.0:
            if raciseE == 1.0:
                return PROBA_PROSTITUTION_TRANSGENRE_ET_RACISEe
            else:
                return PROBA_PROSTITUTION_TRANSGENRE
        else:
            return 0.01

    @staticmethod
    def conditions_prostitution(precarite):
        if precarite > 0.95:
            nombre_clientEs = 25
            tarifs = 20.0
        elif precarite > 0.9:
            nombre_clientEs = 10
            tarifs = 75.0
        elif precarite > 0.8:
            nombre_clientEs = 6
            tarifs = 150.0
        elif precarite > 0.5:
            nombre_clientEs = 4
            tarifs = 250.0
        else:
            nombre_clientEs = 4
            tarifs = 300.0
        return nombre_clientEs, tarifs


    # Créée la ville.
    def __init__(self, largeur, hauteur):

        # Définit la taille de la ville.
        self.largeur = largeur
        self.hauteur = hauteur

        # Initialise les compteurs (variables de classe, au cas où elles n'aient pas été détruites)
        humainE.nombre_total = 0
        humainE.nombre_infecteEs = 0
        humainE.nombre_traiteEs = 0
        humainE.somme_precarite = 0
        humainE.somme_etat_mental = 0

        clientE.nombre_total = 0
        clientE.nombre_infecteEs = 0
        clientE.nombre_traiteEs = 0
        clientE.somme_precarite = 0
        clientE.somme_etat_mental = 0

        prostitueE.nombre_total = 0
        prostitueE.nombre_infecteEs = 0
        prostitueE.nombre_traiteEs = 0
        prostitueE.somme_precarite = 0
        prostitueE.somme_etat_mental = 0

        # Déclare la liste des prostitué.e.s (structure utilisée pour rapidement les retrouver, sans devoir reparcourir
        # tout le tableau ville, lorsque les client.e.s recherchent un.e prostitué.e dans choix_prostitueE).
        self.liste_prostitueEs = []

        # Remplit la ville d'habitant.e.s.
        self.humainEs = [[None for x in range(largeur)] for y in range(hauteur)]
        for x in range(largeur):
            for y in range(hauteur):

                # Définit un.e habitant.e.

                # Préparation de ses caractérstiques.
                alea = random.random()
                if alea < PROPORTION_INFECTEeeS_traiteEs:
                    statut_vih = VIH.INFECTEe_TRAITEe
                elif alea < PROPORTION_INFECTEeeS_traiteEs + PROPORTION_INFECTEeeS_NON_traiteEs:
                    statut_vih = VIH.INFECTEe_NON_TRAITEe
                else:
                    statut_vih = VIH.NON_INFECTEe

                precarite = self.determine_precarite(x, y)
                usage_drogues = self.determine_usage_drogues(precarite)
                raciseE = self.determine_raciseE(precarite)
                transgenre = self.determine_transgenre(precarite)

                # Définit le type de l'habitant.e.
                type = random.random()

                if type<self.proba_prostitution(precarite, transgenre, raciseE):
                    if LEGALISATION:
                        garde_corps = 0.0 if random.random() < 0.5 else 1.0
                        association = 0.0 if random.random() < 0.1 else 1.0
                    else:
                        garde_corps = 0.0 if random.random() < 0.95 else 1.0
                        association = 0.0 if random.random() < 0.3 else 1.0
                    nombre_clientEs, tarifs = self.conditions_prostitution(precarite)
                    habitant = prostitueE(self, statut_vih, precarite, usage_drogues, raciseE, transgenre, x, y, garde_corps, association, nombre_clientEs, tarifs)
                    self.liste_prostitueEs.append(habitant)

                elif type < self.proba_prostitution(precarite, transgenre, raciseE) + PROPORTION_CLIENTeS:
                    dangerosite = random.random()
                    coeff_rayon_recherche_prostitueE = COEFF_RAYON_RECHERCHE_PROSTITUEe
                    proba_viol = COEFF_PROBA_VIOL*dangerosite
                    habitant = clientE(self, statut_vih, precarite, usage_drogues, raciseE, transgenre, x, y,dangerosite, coeff_rayon_recherche_prostitueE, proba_viol)

                else:
                    habitant = humainE(self, statut_vih, precarite, usage_drogues, raciseE, transgenre, x, y)

                # Mémorise cet.te habitant.e.
                self.humainEs[x][y] = habitant

    # Met à jour la ville pour un tour, c'est à dire un mois.
    def simule_un_mois(self):
        for x in range(self.largeur):
            for y in range(self.hauteur):
                self.humainEs[x][y].simule_un_mois()

    # Simule ce qui se passe dans la ville et sa population sur plusieurs tours/mois.
    def simule_plusieurs_mois(self, nombre_tours, stat, numero_simulation):


        # Lance la simulation.
        for tour in range(nombre_tours):

            # La précarité change en fonction des tours...
            prostitueE.somme_precarite = 0
            clientE.somme_precarite = 0
            humainE.somme_precarite = 0
            prostitueE.somme_etat_mental = 0
            clientE.somme_etat_mental = 0
            humainE.somme_etat_mental = 0

            # On veut trier liste_prostitueEs tq. que les prostitué.e.s les plus précaires apparaissent en premier.
            # On utilise la méthode Decorate-Sort-Undecorate.
            # Il est important de le faire à chaque tour car la précarité des prostitué.e.s évolue.
            decorated = [(prostitueE.precarite, i, prostitueE) for i, prostitueE in enumerate(self.liste_prostitueEs)]
            sorted(decorated, reverse = True)
            [prostitueE for precarite, i, prostitueE in decorated] # Undecorate.

            self.simule_un_mois()

            # Met à jour le fichier CSV.
            stat.writerow([
                numero_simulation, tour,
                humainE.nombre_total, humainE.nombre_infecteEs, humainE.nombre_traiteEs,
                humainE.somme_precarite/humainE.nombre_total,
                humainE.somme_etat_mental/humainE.nombre_total,
                clientE.nombre_total, clientE.nombre_infecteEs, clientE.nombre_traiteEs,
                clientE.somme_precarite/clientE.nombre_total,
                clientE.somme_etat_mental/clientE.nombre_total,
                prostitueE.nombre_total, prostitueE.nombre_infecteEs, prostitueE.nombre_traiteEs,
                prostitueE.somme_precarite/prostitueE.nombre_total,
                prostitueE.somme_etat_mental/prostitueE.nombre_total
                ])


        # Affiche un rapport des contaminations au VIH.
        print(
            "Contaminations au VIH après {0} tours :\n"
            "- Sur les {1} clientEs : {2:.1f}% infectéEs dont {3:.1f}% traitéEs\n"
            "- Sur les {4} prostitués : {5:.1f}% infectéEs dont {6:.1f}% traitéEs\n"
            .format(
                nombre_tours,
                clientE.nombre_total,
                clientE.nombre_infecteEs * 100.0 / clientE.nombre_total if clientE.nombre_total != 0 else 0.0,
                clientE.nombre_traiteEs * 100.0 / clientE.nombre_infecteEs if clientE.nombre_infecteEs != 0 else 0.0,
                prostitueE.nombre_total,
                prostitueE.nombre_infecteEs * 100.0 / prostitueE.nombre_total if prostitueE.nombre_total != 0 else 0.0,
                prostitueE.nombre_traiteEs * 100.0 / prostitueE.nombre_infecteEs if prostitueE.nombre_infecteEs != 0 else 0.0))







# Programme principal, pour test.

NOMBRE_DE_SIMULATIONS = 10
NOMBRE_DE_MOIS = 120
LARGEUR = 500
HAUTEUR = 500

# Ce code ne tourne pas sous Python 2
if sys.version_info[0] < 3:
    raise Exception("Python 3 ou superieur requis !")

# Crée l'entête du fichier CSV.
with open("statistiques_tipe.csv", "w", encoding = "UTF8", newline = "") as f:
    stat = csv.writer(f)
    stat.writerow([
    "Simulation", "Tour",
    "Autres", "Infections A", "traitemens A", "precarite A", "etat mental A",
    "Clients", "Infections C", "traitemens C", "precarite C", "etat mental C",
    "Prostitues", "Infections P", "traitemens P", "precarite P", "etat mental p"
    ])



    for numero_simulation in range(NOMBRE_DE_SIMULATIONS):
        ma_ville = ville(LARGEUR, HAUTEUR)
        print("DEBUG: Prostitues (après création de la ville) = {0}\n".format(prostitueE.nombre_total))
        ma_ville.simule_plusieurs_mois(NOMBRE_DE_MOIS, stat, numero_simulation)
        print("DEBUG: Prostitues (après simulation) = {0}\n".format(prostitueE.nombre_total))
        del ma_ville
        print("DEBUG: Prostitues (après destruction de la ville) = {0}\n".format(prostitueE.nombre_total))
        gc.collect()
        print("DEBUG: Prostitues (après \"garbage collection\") = {0}\n".format(prostitueE.nombre_total))



