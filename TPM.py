## for system
from codecs import getencoder
import contextlib
import sys
from this import d
import time
import datetime
import pickle as pick
import csv
from pathlib import Path
import os
import openpyxl
from pandas.core.frame import DataFrame
import xlsxwriter

## for data
import operator
import math
import pandas as pd
import numpy as np
import scipy
import scipy.spatial as sp
from operator import itemgetter
import random
from sklearn.preprocessing import PowerTransformer, minmax_scale

## for visulization
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d.axes3d import Axes3D
import plotly.graph_objs as go
import plotly.express as px
import plotly.figure_factory as ff
from matplotlib.offsetbox import OffsetImage, AnnotationBbox

## for clustering
from sklearn.cluster import KMeans, AgglomerativeClustering, SpectralClustering
from scipy.cluster.hierarchy import dendrogram, linkage, fcluster
from sklearn.preprocessing import normalize
from kmodes.kprototypes import KPrototypes

## for dimension reduction
from sklearn.manifold import MDS
from sklearn.decomposition import PCA

## for summarizing
from statsmodels.stats.weightstats import DescrStatsW

## for R
import rpy2.robjects as ro
from rpy2.robjects import pandas2ri, numpy2ri
#numpy2ri.activate()
#pandas2ri.activate()
from rpy2.robjects.conversion import localconverter
from rpy2.robjects.packages import importr
from rpy2.robjects.lib import grid

#grid.activate()
R = ro.r

R('install.packages("cluster")')
R('install.packages("tidyverse")')
R('install.packages("factoextra")')
R('install.packages("dendextend")')
R('install.packages("stats")')
R('install.packages("base")')
R('install.packages("NbClust")')
R('install.packages("fpc")')
R('install.packages("ggplot2")')
R('install.packages("ggdendro")')
R('install.packages("grDevices")')


r_cluster=importr('cluster')
r_tidyverse=importr('tidyverse')
r_factoextra=importr('factoextra')
r_dendextend=importr('dendextend')
r_stats=importr('stats')
r_base=importr('base')
r_NbClust=importr('NbClust')
r_fpc=importr('fpc')
r_ggplot2=importr('ggplot2')
r_ggdendro=importr('ggdendro')
r_grDevices=importr('grDevices')


def numpy_to_rpy2(numpy):
    with localconverter(ro.default_converter + numpy2ri.converter):
        return ro.conversion.py2rpy(numpy)

def pandas_to_rpy2(dataframe):
    with localconverter(ro.default_converter + pandas2ri.converter):
        return ro.conversion.py2rpy(dataframe)

class DatabasePreparation(object):

    def loadingDatabase(self, url):
        np.seterr(divide='ignore', invalid='ignore')
        self.data = pd.read_csv(url, sep=";", encoding="utf-8")
        print(self.data.head())
        print(self.data.info())        
        self.percent_missing = dict(self.data.isnull().sum() * 100 / len(self.data))
        print(self.percent_missing) 
    
    def preprocessing(self):
        self.data = self.data.drop(['date_visit'], axis = 1) 
        self.data['date_review'] = self.data['date_review'].replace(['0000-00-00'],'0001-01-01')
        self.data['date_review'] = pd.to_datetime(self.data['date_review'], format='%Y-%m-%d', yearfirst = True, errors = 'coerce')
        self.data['country'] = self.data['country'].replace(np.nan, '-', regex=True)
        self.data = self.data[self.data["country"] != "-"]
        self.data = self.data.sort_values('date_review', ascending=True)
        self.data = self.data.dropna(subset=['date_review', 'memberID', 'id', 'age', 'sexe'])
        self.data = self.data.reset_index(drop=True)
        print(self.data.head())
        print(self.data.info())
        self.percent_missing = dict(self.data.isnull().sum() * 100 / len(self.data))
        print(self.percent_missing)
        print(len(self.data.groupby(['id']).groups.keys()))


    def sortTouristsNumberComments(self, limite_commentaires):
        self.dictionnaire = self.data.groupby(['memberID']).groups
        self.dict_sorted = {}
        dict_len = {key: len(value) for key, value in self.dictionnaire.items()}
        sorted_key_list = sorted(dict_len.items(), key=operator.itemgetter(1), reverse=True)
        for i in sorted_key_list:
            if (i[1] < limite_commentaires):
                break
            else:
                self.dict_sorted[i[0]] = self.dictionnaire[i[0]]
        self.data = self.data[self.data['memberID'].isin(list(self.dict_sorted.keys()))]
        self.data =self.data.reset_index(drop=True)
        print(self.data.head())
        print(self.data.info())
        self.percent_missing = dict(self.data.isnull().sum() * 100 / len(self.data))
        print(self.percent_missing)

    def breakdownDatabase(self, breakdown_natio, breakdown_date, date, natio):
        # POUR CONSIDERER TOUTES LES NATIONALITES METTRE A FALSE
        if (breakdown_natio == "True"):
            print("Découpage par nationalité")
            liste_natios = self.data.groupby("country").size().sort_values(ascending = False)
            liste_natios = {k : v for k, v in liste_natios.items()}
            print(list(liste_natios.keys())[0:15])
            self.data = self.data[self.data["country"] == natio]
            self.data = self.data.sort_values('date_review', ascending=True)
            self.data = self.data.reset_index(drop=True)
            print(self.data.head())
            print(self.data.info())
            self.percent_missing = dict(self.data.isnull().sum() * 100 / len(self.data))
            print(self.percent_missing) 
        else:
            print("Pas de découpage par nationalité")

        if (breakdown_date == "True"):
            print("Découpage par année")
            self.data = self.data[self.data['date_review'] >= str(date)+'-01-01']
            self.data = self.data[self.data['date_review'] < str(date+1)+'-01-01']
        else:
            print("Pas de découpage par année")

        self.data = self.data.sort_values('date_review', ascending=True)
        self.data = self.data.reset_index(drop=True) 
        print(self.data.head())
        print(self.data.info())
        self.percent_missing = dict(self.data.isnull().sum() * 100 / len(self.data))
        print(self.percent_missing)

    def locationsList(self, seuil):
        list_locations = self.data.groupby("id").size().sort_values(ascending = False)
        list_locations = {k : v for k, v in list_locations.items()} 
        self.top = []
        if (seuil < len(list_locations.keys())):
            for i in range(0, seuil):
                self.top.append(list(list_locations.keys())[i])
        else:
            print('Erreur, seuil trop grand')

    def run(self, limite_commentaires, breakdown_natio, breakdown_date, date, natio, seuil, url):
        self.loadingDatabase(url)
        self.preprocessing()
        self.sortTouristsNumberComments(limite_commentaires)
        self.breakdownDatabase(breakdown_natio, breakdown_date, date, natio)
        self.locationsList(seuil)
        return self.top

    def locationsDatabase(self, locations, naive = False):
        id_locations = list(locations['id'])
        self.data = self.data[self.data['id'].isin(id_locations)]
        self.data = self.data.reset_index(drop=True)        
        print(self.data.head())
        print(self.data.info())
        self.percent_missing = dict(self.data.isnull().sum() * 100 / len(self.data))
        print(self.percent_missing)
        if naive:
            time = self.data.date_review - self.data.date_review[0]
            self.data.date_review = pd.Series([i.days for i in time])
            self.data = self.data.drop(['nom', 'latitude', 'longitude', 'typeR', 'dateLastScanReviews', 
                                        'gadm36_gid', 'gid', 'name_1', 'name_2', 'name_3', 'name_4', 'name_5',
                                        'region', 'memberID', 'location'], axis = 1)
            self.data = pd.get_dummies(self.data, prefix=['id', 'age', 'sexe', 'country'], columns=['id', 'age', 'sexe', 'country'])
            self.data.date_review = minmax_scale(self.data.date_review)
        return self.data
        
class LocationsClassification(object):

    def loadingClassification(self):
        url = 'data/Classification_locations.csv'
        self.classification = pd.read_csv(url, sep=";", encoding="latin-1")
        print(self.classification.head())
        print(self.classification.info())    

    def differenceClassificationLists(self, top):
        if not list(set(top).difference(list(self.classification.id))):
            print("La différence entre la liste de monuments classifiés et ceux du top est bien nulle")
        else:
            print(list(set(top).difference(list(self.classification.id))))
            print(top)
            sys.exit("La différence entre la liste de monuments classifiés et ceux du top n'est pas nulle !")  

    def creationClassificationCode(self):
        self.classification = self.classification.replace({'Monument' : 'A', 'Park/garden' : 'B', 'Urbanism' : 'C', 
                                    'Art gallerie/museum' : 'D', 'Holy site/place of worship' : 'E',
                                    'Historic building' : 'F', 'Theater/auditorium' : 'G',
                                    'Shop' : 'H', 'Restaurant/bar' : 'I', 'Gastronomy' : 'J',
                                    'Hotel' : 'K', 'Wood' : 'L', 'Watering place' : 'M',
                                    'Beach' : 'N', 'Mountain' : 'O', 'Music building' : 'P',
                                    'Cinema' : 'Q', 'Amusement park/aquarium' : 'R', 'Sport' : 'S', 'Viewpoint' : 'T'}, regex = True)
        self.classification['categorie'] = self.classification['categorie'].str.split('_')

    def run(self, top):
        self.loadingClassification()
        self.differenceClassificationLists(top)
        self.creationClassificationCode()
        return self.classification

    def conversionClassificationId(self, id, data):
        return list(data[data.id == id].categorie)[0]

    def classificationOntology(self, voyage):
        classes = [["A", "B", "C"],
                ["D", "E", "F", "G"],
                ["H", "I", "J", "K"],
                ["L", "M", "N", "O"],
                ["P", "Q", "R", "S"],
                ["T"]]

        index = [np.array(np.pad([voyage.count(j) if j in voyage else 0 for j in i], (0,4-len(i)),'constant', constant_values=0), dtype = 'float') for i in classes]
        return index

class TouristsStaticProfiles(object):

    def staticList(self, data):
        self.static_profiles = list(data.groupby(['memberID', 'country', 'age', 'sexe']).groups.keys())
        self.static_profiles = {i[0]:(i[1], i[2], i[3]) for i in self.static_profiles}

    def run(self, data):
        self.staticList(data)
        return self.static_profiles

class Seasonality(object):
    
    def seasonDetection(self, date):
        self.season = None
        seasons = ["Winter", "Spring", "Summer", "Autumn"]
        
        if ((date.month == 1) or (date.month == 2)):
            self.season = seasons[0]
        else:
            if (date.month == 3):
                if (date.day < 19):
                    self.season = seasons[0]
                else:
                    self.season = seasons[1]
            else:
                if ((date.month == 4) or (date.month == 5)):
                    self.season = seasons[1]
                else:
                    if (date.month == 6):
                        if (date.day < 21):
                            self.season = seasons[1]
                        else:
                            self.season = seasons[2]
                    else:
                        if ((date.month == 7) or (date.month == 8)):
                            self.season = seasons[2]
                        else:
                            if (date.month == 9):
                                if (date.day < 19):
                                    self.season = seasons[2]
                                else:
                                    self.season = seasons[3]
                            else:
                                if ((date.month == 10) or (date.month == 11)):
                                    self.season = seasons[3]
                                else:
                                    if (date.month == 12):
                                        if (date.day < 19):
                                            self.season = seasons[3]
                                        else:
                                            self.season = seasons[0]

    def run(self, date):
        self.seasonDetection(date)
        return self.season

class TripsList(object):

    def touristsProfiles(self, data):
        self.tourists = data.groupby(['memberID']).groups
        self.tourists = dict(sorted(self.tourists.items(), key=operator.itemgetter(0), reverse=True))
        self.tourists_infos = data.groupby(['memberID', 'id', 'date_review']).groups
        self.tourists_infos = dict(sorted(self.tourists_infos.items(), key=operator.itemgetter(0, 0), reverse=True))

    def tripsCreation(self):        
        liste_infos_commentaire = list(self.tourists_infos.keys()) # liste des commentaires contenant pour chaque commentaire le memberID du touriste, 
                                                                    # l'id du monument et la date du commentaire
        liste_index = list(self.tourists_infos.values()) # liste des commentaires contenant l'index de chaque commentaire dans la database 
        self.tourists_raw_dynamic_profiles = {}
        compteur = 0
        for i in self.tourists.items():
            tab = []
            for j in range(compteur, len(liste_index)):
                index = liste_index[j][0]
                if (index in i[1]):
                    date = liste_infos_commentaire[j][2]  
                    id = liste_infos_commentaire[j][1]
                    couple = (date, id)
                    tab.append(couple)
                else:
                    break
            compteur = j
            if (len(tab) > 1):
                self.tourists_raw_dynamic_profiles[i[0]] = sorted(tab, key=lambda x: x[0])

    def tripsOrganisation(self, threshold):
        self.tourists_dynamic_profiles = {}
        seuil = pd.Timedelta(days = threshold)
        for i in self.tourists_raw_dynamic_profiles.items():
            tab1 = []
            tab2 = []
            tab3 = []
            timer = i[1][0][0]      
            for j in range(0, len(i[1])):
                date = i[1][j][0]
                name = i[1][j][1]
                couple = (date, name)
                delta1 = pd.to_timedelta(date.floor('D') - timer.floor('D'))
                tab2.append(couple)
                if (delta1 <= seuil):
                    tab3.extend(tab2)
                    tab2 = []
                    timer = date
                else:
                    if(len(tab3) > 1):
                        tab1.append(tab3)
                    timer = tab2[-1][0]
                    tab3 = []
                    tab3 = tab2
                    tab2 = []     
            if (len(tab3) > 1):
                tab1.append(tab3)
            if (len(tab1) > 0):
                self.tourists_dynamic_profiles[i[0]] = tab1   

    def dynamicProfiles(self, classification):
        classification_data = LocationsClassification()
        season = Seasonality()
        self.dynamic_profiles = {}
        id = 0
        for i in self.tourists_dynamic_profiles.items():
            self.dynamic_profiles[i[0]] = []
            for j in i[1]:
                classifications = []
                saison = season.run(j[0][0])
                duree = j[-1][0] - j[0][0]
                for k in j:
                    classifications.extend(classification_data.conversionClassificationId(k[1], classification))
                self.dynamic_profiles[i[0]].append((classifications, saison, duree, id))
                id = id + 1

    def tripsDatabase(self, classification):
        self.list_trips = {}
        for i in self.dynamic_profiles.items():
            for j in i[1]:
                self.list_trips[j[3]] = (classification.classificationOntology(j[0]), j[1], j[2].days, i[0])
        print("Il y a " + str(len(self.list_trips)) + "trips dans la base de données")

    def dynamicProfilesWithoutClassification(self):
        season = Seasonality()
        self.dynamic_profiles_no_classification = {}
        id = 0
        for i in self.tourists_dynamic_profiles.items():
            self.dynamic_profiles_no_classification[i[0]] = []
            for j in i[1]:
                classifications = []
                saison = season.run(j[0][0])
                duree = j[-1][0] - j[0][0]
                for k in j:
                    classifications.append(k[1])
                self.dynamic_profiles_no_classification[i[0]].append((classifications, saison, duree, id))
                id = id + 1      
                
    def topMonumentsCluster(self, top, clusters, classification, region, date, a, b):
        self.list_locations = {k:[] for k,v in clusters.items()}
        self.list_tops = {k:[] for k,v in clusters.items()}
        for k,v in clusters.items():
            for i in self.dynamic_profiles_no_classification.values():
                if (i[0][-1] in v):
                    self.list_locations[k].extend(i[0][0])
            for i in set(self.list_locations[k]):
                self.list_tops[k].append((i, self.list_locations[k].count(i)))
            self.list_tops[k].sort(key = lambda x: x[1], reverse=True)
            self.list_tops[k] = self.list_tops[k][0:top]
            tpm = []
            for i in self.list_tops[k]:
                tpm.append(list(classification[classification.id == i[0]].nom)[0])
            self.list_tops[k] = tpm
        self.list_tops = pd.DataFrame.from_dict(self.list_tops, orient = "columns")
        print(self.list_tops) 
        self.list_tops.to_csv("res/" + region + "/" + str(date) + "/" + str(a) + "_" + str(b) + "_top.csv", encoding="latin_1")

    def run(self, data, data_classification, threshold, classification):
        self.touristsProfiles(data)
        self.tripsCreation()
        self.tripsOrganisation(threshold)
        self.dynamicProfiles(data_classification)
        self.tripsDatabase(classification)
        return self.list_trips

    def getTop(self, data, threshold, top, clusters, classification, region, date, a, b):
        self.touristsProfiles(data)
        self.tripsCreation()
        self.tripsOrganisation(threshold)
        self.dynamicProfilesWithoutClassification()
        self.topMonumentsCluster(top, clusters, classification, region, date, a, b)

class TripsDatabase(object):
    
    def flatten(self, t):
        return [item for sublist in t for item in sublist]
    
    def visualization_PCA(self, date, region, file, labels):
        color = None
        if (labels is not None):
            if ("color" in self.df.columns):
                self.df.drop(["color"], axis = 1)
            self.df['color'] = labels
            color = 'color'
        fig = px.scatter(self.df, x = "x", y = "y", color = color)
        fig.update_traces(mode="markers")
        fig.show()
        fig.write_html("res/" + region + "/" + str(date) + "/" + file + ".html")

    def database_voyages(self, liste, a, b, date, region):
        new_dict = {k:self.flatten([self.flatten(i) if isinstance(i, list) else [i] for i in v]) for k,v in liste.items()}
        self.database = pd.DataFrame.from_dict(new_dict, orient='index')
        self.database.columns = ["A", "B", "C", "C#", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M", "N", "O", "P", "Q", "R", "S", "T", "T#", "T#2", "T#3", "Saison", "Duree", "Id"]
        self.database[["A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M", "N", "O", "P", "Q", "R", "S", "T", "Duree"]] = minmax_scale(self.database[["A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M", "N", "O", "P", "Q", "R", "S", "T", "Duree"]])
        print(self.database.head())
        print(self.database.info())
        categorical = pd.get_dummies(self.database.Saison)
        self.database_num = self.database.drop(["Saison"], axis = 1)
        self.database_num[["Saison_Autumn",  "Saison_Spring",  "Saison_Summer",  "Saison_Winter"]] = categorical
        self.database_num = self.database_num.drop(["Id"], axis = 1)
        print(self.database_num.head())
        self.matrixProjection(a, b, date, region)
        self.list_trips = {}
        for i in range(0, len(self.database.values)):
            self.list_trips[i] = (np.array([self.database.values[i][j] for j in range(0, 24)]), self.database.values[i][-3], self.database.values[i][-2], self.database.values[i][-1])
        return self.database, self.database_num, self.list_trips
    
    def matrixProjection(self, a, b, date, region):
        mds = MDS(random_state=0, dissimilarity = "euclidean")
        df_transform = pd.DataFrame(mds.fit_transform(self.database_num), columns = ["x", "y"])
        fig = px.scatter(df_transform, x="x", y="y")
        fig.update_traces(mode="markers")
        fig.show()
        fig.write_html("res/" + region + "/" + str(date) + "/" + str(a) + "_" + str(b) + "_" + "projection.html")

    def embedding_PCA(self, date, region):
        pca = PCA(n_components=2)
        self.df = pd.DataFrame(pca.fit_transform(self.database_num), columns = ["x", "y"])
        self.visualization_PCA(date, region, "pca", None)

    def run(self, liste, a, b, date, region):
        self.database_voyages(liste, a, b, date, region)
        #self.embedding_PCA(date, region)

class AlgoClustering(object):

    def hierarchical_clustering(self, database, k, date, region):
        modelhierarchical = AgglomerativeClustering(n_clusters=k)
        modelhierarchical.fit_predict(database)
        #self.matrixProjection(a = "hierarchical", b = "", date = date, region = region, database = database)
        return modelhierarchical.labels_

    def kmeans_clustering(self, database, k, date, region):
        modelkmeans = KMeans(n_clusters = k, init = 'k-means++', n_init = 100)
        modelkmeans.fit_predict(database)
        #self.matrixProjection(a = "kmeans", b = "", date = date, region = region, database = database)
        return modelkmeans.labels_

    def spectral_clustering(self, database, k, date, region):
        modelspectral = SpectralClustering(n_clusters= k, assign_labels='cluster_qr')
        modelspectral.fit_predict(database)
        #self.matrixProjection(a = "spectral", b = "", date = date, region = region, database = database)
        return modelspectral.labels_

    def kprototypes_clustering(self, database, k, date, region):
        modelkproto = KPrototypes(n_clusters = k, init='Cao', n_jobs = 4)
        modelkproto.fit_predict(database, categorical=[24])
        #self.matrixProjection(a = "kmeans", b = "", date = date, region = region, database = database)
        return modelkproto.labels_
    
    def matrixProjection(self, a, b, date, region, database):
        mds = MDS(random_state=0, dissimilarity = "euclidean")
        df_transform = pd.DataFrame(mds.fit_transform(database), columns = ["x", "y"])
        fig = px.scatter(df_transform, x="x", y="y")
        fig.update_traces(mode="markers")
        fig.show()
        fig.write_html("res/" + region + "/" + str(date) + "/" + str(a) + "_" + str(b) + "_" + "projection.html")

class TouristProfileMeasure(object):
    
    def distanceMatrix(self, list_trips, a, b):
        content_matrix = np.zeros((len(list_trips), len(list_trips)))
        context_matrix = np.zeros((len(list_trips), len(list_trips)))
        start_time = time.time()
        tabA1 = np.array([i[0] for i in list_trips.values()]) #monumentcat
        tabB1 = np.array([i[1] for i in list_trips.values()]) #saison
        tabC1 = np.array([i[2] for i in list_trips.values()]) #duree

        for i in range(0, len(list_trips) - 1):
            idA = list_trips[i][0] #monument
            idB = list_trips[i][1] #saison
            idC = list_trips[i][2] #duree

            tabA = tabA1[i+1:] #monumentcat
            tabB = tabB1[i+1:] #saison
            tabC = tabC1[i+1:] #duree

            resA = self.classificationDistance(tabA, idA)
            resB = self.seasonDistance(tabB, idB)
            resC = self.durationDistance(tabC, idC)

            content_matrix[i+1:,i] = resA
            context_matrix[i+1:,i] = resB + resC
        
        content_matrix = content_matrix/np.max(content_matrix)
        context_matrix = context_matrix/np.max(context_matrix)
        self.matrix = a*content_matrix + b*context_matrix
        self.matrix = normalize(self.matrix, axis=1, norm='l1')
        #self.tril = matrix.T[np.triu_indices_from(matrix.T, 1)] #On transpose la matrice pour récupérer les éléments de la matrice dans leurs 
                                                            #ordres d'insertion !!
        self.r_matrix = numpy_to_rpy2(self.matrix)
        self.r_tril = r_stats.as_dist(self.r_matrix, diag = False, upper = False)
        print("--- %s seconds ---" % (time.time() - start_time)) 
        return self.r_tril

    def entanglementMatrix(self, list_trips):
        self.ent = np.zeros((11, 11))
        start_time = time.time()
        for score_a in range(0, 11): 
            score_b = 1 - score_a/10
            score_a = score_a/10
            score_a = round(score_a,1)
            score_b = round(score_b,1)
            self.distanceMatrix(list_trips, score_a, score_b)
            Path("matrice").mkdir(parents=True, exist_ok=True)    
            with open("matrice/" + str(score_a) + "_" + str(score_b) + ".pkl", "wb") as tf:
                pick.dump(self.matrix, tf)
        
        for i in range(0, 11):
            print(i)
            with open("matrice/" + str(round(i/10,1)) + "_" + str(round(1 - i/10,1)) + ".pkl", "rb") as tf: #i puis i puisque la matrice d'intrication est symétrique
                matrix_a = pick.load(tf)
            print(matrix_a)
            r_matrix_a = numpy_to_rpy2(matrix_a)
            r_tril_a = r_stats.as_dist(r_matrix_a, diag = False, upper = False)
            r_hc_a =  r_stats.hclust(r_tril_a, "ward.D2")
            r_dend_a = r_stats.as_dendrogram(r_hc_a)
            print(self.ent)
            print("--- %s seconds ---" % (time.time() - start_time))
            for j in range(i, 11):
                print(j)
                with open("matrice/" + str(round(j/10,1)) + "_" + str(round(1 - j/10,1)) + ".pkl", "rb") as tf:
                    matrix_b = pick.load(tf)
                r_matrix_b = numpy_to_rpy2(matrix_b)
                r_tril_b = r_stats.as_dist(r_matrix_b, diag = False, upper = False)
                r_hc_b =  r_stats.hclust(r_tril_b, "ward.D2")
                r_dend_b = r_stats.as_dendrogram(r_hc_b)
                dend_list = r_dendextend.dendlist(r_dend_a, r_dend_b)
                dend_list = r_dendextend.untangle(dend_list, method = "random")
                ent_value = float(r_dendextend.entanglement(dend_list)[0])
                self.ent[i, j] = round(ent_value, 3)
                print("--- %s seconds ---" % (time.time() - start_time))
        
    def entanglementVisualization(self, date, region):
        v = self.ent[np.triu_indices(self.ent.shape[0], k = 0)]
        nr, nc = self.ent.shape
        matrice = np.zeros((nr,nc))
        matrice[np.triu_indices(matrice.shape[0], k = 0)] = v
        matrice = matrice + matrice.T - np.diag(np.diag(matrice))
        print(matrice)
        x=np.arange(0,1.1,0.1)
        y=np.arange(0,1.1,0.1)
        #y = 1 - y
        fig = px.imshow(matrice, text_auto=True,
        x = ["(1.0,0.0)", "(0.9,0.1)", "(0.8,0.2)", "(0.7,0.3)", "(0.6,0.4)", "(0.5,0.5)", "(0.4,0.6)", "(0.3,0.7)", "(0.2,0.8)", "(0.1,0.9)", "(0.0,1.0)"], 
        y = ["(1.0,0.0)", "(0.9,0.1)", "(0.8,0.2)", "(0.7,0.3)", "(0.6,0.4)", "(0.5,0.5)", "(0.4,0.6)", "(0.3,0.7)", "(0.2,0.8)", "(0.1,0.9)", "(0.0,1.0)"], 
        labels={"x" : "First hyperparameter couple", "y": "Second hyperparameter couple"})
        fig.show()
        fig.write_html("res/" + region + "/" + str(date) + "_" + "entanglement.html")

    def matrixProjection(self, a, b, date, region):
        matrice = self.matrix + self.matrix.T - np.diag(np.diag(self.matrix))
        mds = MDS(random_state=0, dissimilarity = "precomputed")
        df_transform = pd.DataFrame(mds.fit_transform(matrice), columns = ["x", "y"])
        fig = px.scatter(df_transform, x="x", y="y")
        fig.update_traces(mode="markers")
        fig.show()
        fig.write_html("res/" + region + "/" + str(date) + "/" + str(a) + "_" + str(b) + "_" + "projection.html")

    def classificationDistance(self, tab, id, distance = "euclidean"):
        res = None
        if (distance == "euclidean"):
            sub = tab - id
            res = np.sum(np.sqrt(np.einsum('ki,ki->ki', sub, sub)), axis = 1)
            #res = np.sum(np.sqrt(np.einsum('kij,kij->ki', sub, sub)), axis = 1)
        else:
            if (distance == "cosine"):
                res = np.sum(1 - np.nan_to_num((np.einsum('kij,ij->ki', tab, id)/(np.linalg.norm(tab, axis=2)*np.linalg.norm(id, axis=1))), nan = 1), axis = 1)
        return res
    
    def seasonDistance(self, tab, id, distance = "graph"):
        saisons = {"Winter":0, "Spring":1, "Summer":2, "Autumn":3}
        res = None
        if (distance == "discrete"):
            res = [int(id == i) for i in tab]
        else:
            if (distance == "graph"):
                res = 1 - abs(1 - abs(saisons[id] - np.array(itemgetter(*tab)(saisons)))/2)
        return res
    
    def durationDistance(self, tab, id):        
        res = np.sqrt((tab - id)**2)
        return res 
    
    def hierarchicalClustering(self, k):
        r_hc = r_stats.hclust(self.r_tril, method = "ward.D2")
        self.r_groups = r_dendextend.cutree(r_hc, k)
        #self.cluster = fcluster(Z = self.linked, t = self.k, criterion = "maxclust")       
    
    def run(self, list_trips, a, b, date, region, k):
        self.distanceMatrix(list_trips, a, b)
        self.matrixProjection(a, b, date, region)
        self.hierarchicalClustering(k)
        return self.r_groups
    
    def entanglement(self, list_trips, date, region):
        self.entanglementMatrix(list_trips)
        self.entanglementVisualization(date, region)

class ClusteringMeasures(object):

    def numberClusters(self, a, b, date, region, database):
        r_database = pandas_to_rpy2(database)
        #r_index = r_base.list('dunn', 'silhouette', 'frey', 'mcclain', "cindex")
        #r_index = r_base.list('sdbw')
        r_index = r_base.list('silhouette')
        r_length = r_base.length(r_index)
        r_liste = r_base.vector("list", r_length)
        min = 2
        max = 15
        for i in range(0,r_length[0]):
            #r_nb = r_NbClust.NbClust(data = ro.NULL, diss = r_tril, method = "ward.D2", distance = ro.NULL, min_nc = min, max_nc = max, index = r_index[i])
            r_nb = r_NbClust.NbClust(data = r_database, method = "ward.D2", distance = "euclidean", min_nc = min, max_nc = max, index = r_index[i]) #pour algo usuels
            #r_liste[i] = r_nb.rx('Best.nc')[0]
            #r_liste[i] = r_liste[i].rx('Number_clusters')
            r_liste[i] = r_nb.rx('All.index')
        x = np.array(r_liste[0])[0]
        y = np.arange(min,max+1)
        df = pd.DataFrame([x,y])
        df = df.transpose()
        df.columns = ['y', 'x']
        Path("res/" + region + "/" + str(date)).mkdir(parents=True, exist_ok=True)
        fig = px.scatter(df, x="x", y="y")
        fig.update_traces(mode="markers+lines")
        fig.write_html("res/" + region + "/" + str(date) + "/" + str(a) + "_" + str(b) + "_" + "silhouette.html")
        fig.show()
        
        #self.k = r_base.mean(r_base.unlist(r_liste))
        #self.k = round(float(self.k[0]))
        self.k = float(input('Quel est la valeur de k ?'))
        internal = list(df[df.x == self.k].y)[0]
        return self.k, internal
    
    def run(self, a, b, distance_classification, distance_season, date, region, database):
        self.numberClusters(a, b, distance_classification, distance_season, date, region, database)

class TPMAlgorithm(object):
        
    def extractionClusters(self, r_groups):
        groups = list(r_groups)
        maximum = max(groups)
        minimum = min(groups)
        id = list(range(minimum, maximum + 1))
        cluster = [0]*len(id)
        zip_iterator = zip(id, cluster)
        self.clusters = dict(zip_iterator)
        for i in range(0, len(groups)):
            if (self.clusters[groups[i]] == 0):
                self.clusters[groups[i]] = []
                self.clusters[groups[i]].append(i)
            else:
                self.clusters[groups[i]].append(i)

    def informationMerge(self, list_trips, static):
        self.profiles = {}
        for i in self.clusters.items():
            tab = []
            for j in i[1]:
                tab.append((list_trips[j][:-1] + static[list_trips[j][-1]]))
            self.profiles[i[0]] = tab

    def summaryClusters(self):
        classes = [['Monument', 'Park/garden', 'Urbanism'],
            ['Art gallerie/museum', 'Holy site/place of worship', 'Historic building', 'Theater/auditorium'],
            ['Shop', 'Restaurant/bar', 'Gastronomy', 'Hotel'],
            ['Wood', 'Watering place', 'Beach', 'Mountain'],
            ['Music building', 'Cinema', 'Amusement park/aquarium', 'Sport'],
            ["Viewpoint"]]
        self.summary = {}
        self.natio = []
        cluster = 1
        for i in self.profiles.items():
            size = len(i[1])
                   
            comments = {}        
            for j in i[1]:
                com = 0
                for k in j[0]:
                    com = com + np.sum(k)
                if(com in comments.keys()):
                    comments[com] = comments[com] + 1
                else:
                    comments[com] = 1
            weighted_stats = DescrStatsW(list(comments.keys()), weights=list(comments.values()), ddof=0)

            locations = {}
            for a in i[1]:
                for b in range(0, len(a[0])):
                    for c in range(0, len(classes[b])): #on doit itérer sur classes plutot que sur a[0][b] du fait 
                                                        #de la taille standardisée des vecteurs de classification
                        classe = classes[b][c]
                        if (classe in locations.keys()):
                            locations[classe] = locations[classe] + a[0][b][c]
                        else:
                            locations[classe] = 1
            locations = {k:round((v/np.sum(np.array(list(locations.values()))))*100, 3) for k,v in locations.items()}
            locations = dict(sorted(locations.items(), key=operator.itemgetter(0), reverse=False))

            seasons = {}    
            for l in i[1]:
                if (l[1] in seasons.keys()):
                    seasons[l[1]] = seasons[l[1]] + 1
                else:
                    seasons[l[1]] = 1
            seasons = {k:round((v/size)*100, 3) for k,v in seasons.items()}
            seasons = dict(sorted(seasons.items(), key=operator.itemgetter(1), reverse=True)) 

            durations = [j[2] for j in i[1]] 

            nationalities = {}
            for m in i[1]:
                if (m[3] in nationalities.keys()):
                    nationalities[m[3]] = nationalities[m[3]] + 1
                else:
                    nationalities[m[3]] = 1
            nationalities = {k:round((v/size)*100, 3) for k,v in nationalities.items()}
            nationalities = dict(sorted(nationalities.items(), key=operator.itemgetter(1), reverse=True)[0:10])
            nationalities = dict(sorted(nationalities.items(), key=operator.itemgetter(0), reverse=False))
            self.natio.extend(list(nationalities.keys()))
            
            ages = {}
            for n in i[1]:
                if (n[4] in ages.keys()):
                    ages[n[4]] = ages[n[4]] + 1
                else:
                    ages[n[4]] = 1
            ages = {k:round((v/size)*100, 3) for k,v in ages.items()}
            ages = dict(sorted(ages.items(), key=operator.itemgetter(1), reverse=True))             

            sexes = {}
            for o in i[1]:
                if (o[5] in sexes.keys()):
                    sexes[o[5]] = sexes[o[5]] + 1
                else:
                    sexes[o[5]] = 1
            sexes = {k:round((v/size)*100, 3) for k,v in sexes.items()}
            sexes = dict(sorted(sexes.items(), key=operator.itemgetter(1), reverse=True))             

            self.summary[i[0]] = {"Cluster" : cluster,
                            "Duration_Mean" : round(np.mean(durations), 3), 
                            "Duration_Standard_Deviation" : round(np.std(durations), 3),
                            "Comments_Mean": round(weighted_stats.mean, 3),
                            "Comments_Standard_Deviation": round(weighted_stats.std, 3),
                            "Taille": size,
                            "Summer" : 0,
                            "Autumn" : 0,
                            "Winter" : 0,
                            "Spring" : 0,
                            "man" : 0,
                            "woman" : 0,
                            "35-49" : 0,
                            "50-64" : 0,
                            "25-34" : 0,
                            "18-24" : 0,
                            "13-17" : 0,
                            "4-2a" : 0,
                            'Monument' : 0, 
                            'Park/garden' : 0, 
                            'Urbanism' : 0, 
                            'Art gallerie/museum' : 0, 
                            'Holy site/place of worship' : 0,
                            'Historic building' : 0, 
                            'Theater/auditorium' : 0,
                            'Shop' : 0, 
                            'Restaurant/bar' : 0, 
                            'Gastronomy' : 0,
                            'Hotel' : 0, 
                            'Wood' : 0, 
                            'Watering place' : 0,
                            'Beach' : 0, 
                            'Mountain' : 0, 
                            'Music building' : 0,
                            'Cinema' : 0, 
                            'Amusement park/aquarium' : 0, 
                            'Sport' : 0, 
                            'Viewpoint' : 0}
            
            self.summary[i[0]].update(seasons)
            self.summary[i[0]].update(locations)
            self.summary[i[0]].update(nationalities)
            self.summary[i[0]].update(ages)
            self.summary[i[0]].update(sexes)
            cluster = cluster + 1
        self.natio = list(set(self.natio))
        self.natio = dict.fromkeys(self.natio, 0)
        for i in self.profiles.items():
            res = self.natio.copy()
            res.update(self.summary[i[0]])
            self.summary[i[0]] = res

        mean = np.array([[np.sum([self.summary[i][j] if j == k else 0 for j in self.summary[i].keys()]) for i in self.summary.keys()] for k in self.summary[1].keys()])
        mean_size = np.array([[np.sum([self.summary[i][j] if j == "Taille" else 0 for j in self.summary[i].keys()]) for i in self.summary.keys()]])
        self.summary["Mean"] = dict(zip(list(self.summary[1].keys()), np.around(np.sum(mean*mean_size, axis = 1)/np.sum(mean_size), 3)))
        self.summary["Mean"]["Cluster"] = "Mean"

    def saveResults(self, a, b, date, region):
        path = "res/" + region + "/" + str(date) + "/"        
        file = str(a) + "_" + str(b)
        Path(path).mkdir(parents=True, exist_ok=True)
        with open(path + file + "_clusters.pkl", "wb") as tf:
            pick.dump(self.clusters,tf)
        
        self.summary = list(self.summary.values())
        with open(path + file + "_summary.pkl", "wb") as tf:
            pick.dump(self.summary,tf)  
    
    def openResults(self, a, b, date, region, file):
        #file = input("Ouvrir summary ou clusters ?")
        path = "res/" + region + "/" + str(date)
        file = str(a) + "_" + str(b) + "_" + file + ".pkl"
        with open(path + file, "rb") as tf:
            new_dict = pick.load(tf)
        return new_dict

    def convertSummaryToCsv(self, a, b, date, region):
        csv_columns = list(self.summary[1].keys())
        path = "res/" + region + "/" + str(date)
        file = str(a) + "_" + str(b) + "_clusters.csv"
        Path(path).mkdir(parents=True, exist_ok=True)
        csv_file = path + "/" + file

        try:
            with open(csv_file, 'w') as csvfile:
                writer = csv.DictWriter(csvfile, fieldnames=csv_columns)
                writer.writeheader()
                for data in self.summary:
                    writer.writerow(data)
        except IOError:
            print("I/O error")
    
    def convertCsvToExcel(self, a, b, date, region):
        path = "res/" + region + "/" + str(date)
        file = str(a) + "_" + str(b) + "_clusters.csv"
        data = pd.read_csv(path + '/' + file)
        data = pd.pivot_table(data,index=["Cluster"])

        saisons = data[['Winter', 'Spring', 'Autumn', 'Summer']]
        durees = data[["Duration_Mean", "Duration_Standard_Deviation"]]
        attractions = data[['Monument', 'Park/garden', 'Urbanism',
                            'Art gallerie/museum', 'Holy site/place of worship', 'Historic building', 'Theater/auditorium',
                            'Shop', 'Restaurant/bar', 'Gastronomy', 'Hotel',
                            'Wood', 'Watering place', 'Beach', 'Mountain',
                            'Music building', 'Cinema', 'Amusement park/aquarium', 'Sport',
                            "Viewpoint"]]
        commentaires = data[['Taille', "Comments_Mean", "Comments_Standard_Deviation"]]
        demographiques = data[["man","woman","35-49","50-64","25-34","18-24","13-17","4-2a"]]
        nationalites = data.drop(['Winter', 'Spring', 'Autumn', 'Summer', "Duration_Mean", "Duration_Standard_Deviation", 'Monument', 'Park/garden', 'Urbanism',
                            'Art gallerie/museum', 'Holy site/place of worship', 'Historic building', 'Theater/auditorium',
                            'Shop', 'Restaurant/bar', 'Gastronomy', 'Hotel',
                            'Wood', 'Watering place', 'Beach', 'Mountain',
                            'Music building', 'Cinema', 'Amusement park/aquarium', 'Sport',
                            "Viewpoint", 'Taille', "Comments_Mean", "Comments_Standard_Deviation", 
                            "man","woman","35-49","50-64","25-34","18-24","13-17","4-2a"], 1)
        
        path = "res/" + region + "/" + str(date)
        file = str(a) + "_" + str(b) + "_clusters.xlsx"
        excelfilename = path + "/" + file
        Path(path).mkdir(parents=True, exist_ok=True)

        liste = [saisons, durees, attractions, commentaires, demographiques, nationalites]
        names = ["saisons", "durees", "attractions", "commentaires", "demographiques", "nationalites"]

        try:
            os.remove(excelfilename)
        except OSError:
            pass

        writer = pd.ExcelWriter(excelfilename, engine='xlsxwriter')
        for i in range (0, len(liste)):
            file = liste[i]
            name = names[i]
            file.to_excel(writer, index=True, sheet_name=name)
        writer.save()


    def run(self, list_trips, static, a, b, date, region, r_groups):
        self.extractionClusters(r_groups)
        self.informationMerge(list_trips, static)
        self.summaryClusters()
        self.saveResults(a, b, date, region)
        self.convertSummaryToCsv(a, b, date, region)
        self.convertCsvToExcel(a, b, date, region)

class NaiveAlgorithm(object):
        
    def extractionClusters(self, groups):
        maximum = max(groups)
        minimum = min(groups)
        id = list(range(minimum, maximum + 1))
        cluster = [0]*len(id)
        zip_iterator = zip(id, cluster)
        self.clusters = dict(zip_iterator)
        for i in range(0, len(groups)):
            if (self.clusters[groups[i]] == 0):
                self.clusters[groups[i]] = []
                self.clusters[groups[i]].append(i)
            else:
                self.clusters[groups[i]].append(i)

    def informationMerge(self, database, classification):
        self.profiles = {}
        for i in self.clusters.items():
            tab = []
            for j in i[1]:
                data = database[database.index == j]
                tab.append((database_classification[database_classification.id == data.id.values[0]].nom.values[0], data.date_review.values[0], data.sexe.values[0], 
                            data.age.values[0], data.country.values[0]))
            self.profiles[i[0]] = tab

    def summaryClusters(self):
        self.summary = {}
        self.natio = []
        self.loca = []
        cluster = 1
        for i in self.profiles.items():
            locations = [j[0] for j in i[1]]
            locations = {item:locations.count(item) for item in locations}
            locations = dict(sorted(locations.items(), key=operator.itemgetter(1), reverse=True))
            locations = {k:round((v/np.sum(np.array(list(locations.values()))))*100, 3) for k,v in locations.items()}
            locations = dict(list(locations.items())[0: 10])
            self.loca.extend(list(locations.keys()))

            date = pd.DataFrame([j[1] for j in i[1]], columns=["date"]).date
            m = pd.Timestamp(0)
            mean = (m + (date - m).mean()).floor('s')
            

            gender = [j[2] for j in i[1]]
            gender = {item:gender.count(item) for item in gender}
            gender = dict(sorted(gender.items(), key=operator.itemgetter(1), reverse=True)) 
            gender = {k:round((v/np.sum(np.array(list(gender.values()))))*100, 3) for k,v in gender.items()}

            age = [j[3] for j in i[1]]
            age = {item:age.count(item) for item in age}
            age = dict(sorted(age.items(), key=operator.itemgetter(1), reverse=True))
            age = {k:round((v/np.sum(np.array(list(age.values()))))*100, 3) for k,v in age.items()}

            nationalites = [j[4] for j in i[1]]
            nationalites = {item:nationalites.count(item) for item in nationalites}
            nationalites = dict(sorted(nationalites.items(), key=operator.itemgetter(1), reverse=True))
            nationalites = {k:round((v/np.sum(np.array(list(nationalites.values()))))*100, 3) for k,v in nationalites.items()} 
            nationalites = dict(list(nationalites.items())[0: 10])
            self.natio.extend(list(nationalites.keys()))

            self.summary[i[0]]={"Cluster" : cluster,
                                "Taille": len(i[1]),
                                "Date_Mean" : mean,
                                "man" : 0,
                                "woman" : 0,
                                "35-49" : 0,
                                "50-64" : 0,
                                "25-34" : 0,
                                "18-24" : 0,
                                "13-17" : 0,
                                "4-2a" : 0}
            
            self.summary[i[0]].update(locations)
            self.summary[i[0]].update(gender)
            self.summary[i[0]].update(age)
            self.summary[i[0]].update(nationalites)
            cluster = cluster + 1
        self.natio = list(set(self.natio))
        self.natio = dict.fromkeys(self.natio, 0)
        for i in self.profiles.items():
            res = self.natio.copy()
            res.update(self.summary[i[0]])
            self.summary[i[0]] = res
        
        self.loca = list(set(self.loca))
        self.loca = dict.fromkeys(self.loca, 0)
        for i in self.profiles.items():
            res = self.loca.copy()
            res.update(self.summary[i[0]])
            self.summary[i[0]] = res

        keys = list(self.summary[1].keys())
        #keys.remove("Date_Mean")
        m = pd.to_datetime(0)
        date_mean = pd.DataFrame([j["Date_Mean"] for j in self.summary.values()], columns = ["date"]).date
        date_mean = (m + (date_mean - m).mean()).floor('s')
        mean = np.array([[np.sum([self.summary[i][j] if ((j == k) and (k != "Date_Mean"))  else 0 for j in self.summary[i].keys()]) for i in self.summary.keys()] for k in keys])
        mean_size = np.array([[np.sum([self.summary[i][j] if j == "Taille" else 0 for j in self.summary[i].keys()]) for i in self.summary.keys()]])
        self.summary["Mean"] = dict(zip(keys, np.around(np.sum(mean*mean_size, axis = 1)/np.sum(mean_size), 3)))
        self.summary["Mean"]["Cluster"] = "Mean"
        self.summary["Mean"]["Date_Mean"] = date_mean

    def saveResults(self, date, region, algo):
        path = "res/" + region + "/" + str(date) + "/"        
        file = algo
        Path(path).mkdir(parents=True, exist_ok=True)
        with open(path + file + "_clusters.pkl", "wb") as tf:
            pick.dump(self.clusters,tf)
        
        self.summary = list(self.summary.values())
        with open(path + file + "_summary.pkl", "wb") as tf:
            pick.dump(self.summary,tf)  
    
    def openResults(self, date, region, algo, file):
        #file = input("Ouvrir summary ou clusters ?")
        path = "res/" + region + "/" + str(date) + "/"
        file = algo + "_" + file + ".pkl"
        with open(path + file, "rb") as tf:
            new_dict = pick.load(tf)
        return new_dict

    def convertSummaryToCsv(self, date, region, algo):
        csv_columns = list(self.summary[1].keys())
        path = "res/" + region + "/" + str(date) + "/"
        file = algo + "_clusters.csv"
        Path(path).mkdir(parents=True, exist_ok=True)
        csv_file = path + "/" + file

        try:
            with open(csv_file, 'w', encoding='latin') as csvfile:
                writer = csv.DictWriter(csvfile, fieldnames=csv_columns)
                writer.writeheader()
                for data in self.summary:
                    writer.writerow(data)
        except IOError:
            print("I/O error")
    
    def convertCsvToExcel(self, date, region, algo):
        path = "res/" + region + "/" + str(date) + "/"
        file = algo + "_clusters.csv"
        data = pd.read_csv(path + '/' + file, encoding='latin')
        date_mean = data["Date_Mean"].values
        data = pd.pivot_table(data, index=["Cluster"])
        data["Date_Mean"] = date_mean #OBLIGATOIRE !! La colonne Date_Mean n'est pas inclue dans le pivor table sinon ... (aucune idée de pourquoi ...)

        date_mean = data[['Date_Mean']]
        commentaires = data[['Taille']]
        demographiques = data[["man","woman","35-49","50-64","25-34","18-24","13-17","4-2a"]]
        locations = data[list(self.loca.keys())]
        nationalites = data[list(self.natio.keys())]
        
        path = "res/" + region + "/" + str(date) + "/"
        file = algo + "_clusters.xlsx"
        # file = "Hierarchical_clusters.xlsx"
        excelfilename = path + "/" + file
        Path(path).mkdir(parents=True, exist_ok=True)

        liste = [date_mean, locations, commentaires, demographiques, nationalites]
        names = ["date", "locations", "commentaires", "demographiques", "nationalites"]

        try:
            os.remove(excelfilename)
        except OSError:
            pass

        writer = pd.ExcelWriter(excelfilename, engine='xlsxwriter')
        for i in range (0, len(liste)):
            file = liste[i]
            name = names[i]
            file.to_excel(writer, index=True, sheet_name=name)
        writer.save()


    def run(self, data, date, region, groups, algo, classification):
        self.extractionClusters(groups)
        self.informationMerge(data, classification)
        self.summaryClusters()
        self.saveResults(date, region, algo)
        self.convertSummaryToCsv(date, region, algo)
        self.convertCsvToExcel(date, region, algo)

if __name__ == '__main__':

    database = DatabasePreparation()
    classification = LocationsClassification()
    trips = TripsList()
    static = TouristsStaticProfiles()
    tpm = TouristProfileMeasure()
    df = TripsDatabase()
    algo = TPMAlgorithm()
    measures = ClusteringMeasures()
    naiveAlgo = NaiveAlgorithm()
    usual = AlgoClustering()

    '''
    limite_commentaires = int(input("Quelle est le seuil minimum de commentaires par touriste ?"))
    breakdown = str(input("Découpage par nationalité : True/False?"))
    date = int(input("Quelle est la date ?"))
    seuil = int(input("Quel est le nombre de monument à considérer ?"))
    '''

    url_idf = 'data/Reviews_Ile_de_France.csv'
    url_hdf = 'data/Reviews_Hauts_de_France.csv'

    #region = "Hauts_de_France"  
    region = "Ile_de_France"
    #   
    # NOMBRE DE COMMENTAIRES MINIMUM POUR QU'UN TOURISTE SOIT CONSIDERE
    limite_commentaires = 4
    breakdown_natio = "False"
    breakdown_date = "True"
    natio = None
    date = 2018

    # LIMITE DE MONUMENTS A CONSIDERER
    seuil = 20
    top = database.run(limite_commentaires, breakdown_natio, breakdown_date, date, natio, seuil, url = url_idf)
    database_classification = classification.run(top)
    data = database.locationsDatabase(database_classification)  
    naive = database.locationsDatabase(database_classification, naive=True)


# # Algorithmes usuels ####################
    '''
    k, internal = measures.numberClusters(a = "usual", b = "", date = date, region = region, database = naive)
    
    spectral = usual.kmeans_clustering(naive, int(k), date, region)
    naiveAlgo.run(data, date, region, spectral, algo = "spectral", classification = database_classification)

    kmeans = usual.kmeans_clustering(naive, int(k), date, region)
    naiveAlgo.run(data, date, region, kmeans, algo = "kmeans", classification = database_classification)

    hierarchical = usual.hierarchical_clustering(naive, int(k), date, region)
    naiveAlgo.run(data, date, region, hierarchical, algo = "hierarchical", classification = database_classification)
    '''
#      

# ####################

    #threshold = int(input("Quelle est la limite de jour pour un voyage ?"))
    threshold = 7
#    list_trips = trips.getTop(data, threshold, 10, clusters, database_classification, region, date = "2015-2018", a = 0.8, b = 0.2)
    list_trips = trips.run(data, database_classification, threshold, classification)
    list_static = static.run(data)
    
#     '''
#     distance_classification = input("Quelle est la distance entre les vecteurs de classification : euclidean ou cosine ?")
#     distance_season = input("Quelle est la distance entre les saisons : discrete ou graph ?")
#     '''

    distance_classification = "euclidean"
    distance_season = "discrete"

#     '''
#     a = float(input("Quelle est la valeur du paramètre a ?"))
#     b = float(input("Quelle est la valeur du paramètre b ?"))
#     '''
    data, data_num, list_trips_norm = df.database_voyages(list_trips, a = "stays_dataset", b = "", date = date, region = region)

    # # Number of clusters ####################
    
    '''    
    #k, internal = measures.numberClusters(a = "TPM", b = "", date = date, region = region, database = data_num) #algo usuels
    print(internal)
    '''
    k = 7
    # #################### 

    for i in range(0, 11, 2):
        a = i/10
        b = 1 - a

    # # TPM Algorithme ####################
        r_tril = tpm.distanceMatrix(list_trips=list_trips_norm, a = a, b = b)
        k, internal = measures.numberClusters(a = "TPM", b = "", date = date, region = region, database = data_num)
        print(internal)

        r_groups = tpm.run(list_trips_norm, a, b, date, region, k)
        algo.run(list_trips, list_static, a, b, date, region, r_groups)
        print("DONE")
        
    # ####################

    # # Intrication ####################

    #     #tpm.entanglement(list_trips_norm, date, region)

    # ####################