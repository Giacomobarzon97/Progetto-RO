set Prodotti;
set Giorni ordered;
set Stati ordered;

#Dichiarazione Parametri

#Prezzi di vendita delle componenti
param v{Prodotti};
#Costo orario delle macchine
param c{Stati};
#produzione orari delle macchine in relazione a ciascun prodotto
param po{Prodotti, Stati};
#Numero minimo unita' richieste dal cliente
param minUnit{Prodotti};
#Penali da pagare per ogni unita' di prodotto non recapitata
param penale{Prodotti};
#Numero di unita' grezze di partenza
param startingUnits{Prodotti};
#Numero di ore massimo in cui e' possibile utilizzare i macchinari
param o;

param M=8;

#Dichiarazione Variabili

#Numero di ore in cui il macchinario e' attivo 
#su un determinato prodotto un determinato giorno
var x{Prodotti, Stati, Giorni}>=0;
#Numero di componenti di un determinato tipo in
#un determinato stato prodotti durante uno specifico giorno
var y{Prodotti, Stati, Giorni}>=0 integer;
#Numero di unita' non recapitate
var ma{Prodotti}>=0 integer;
#Variabile binaria che vale 1 se la macchina 
#ha lavorato ad un prodotto p il giorno g 0 altrimenti
var z{Prodotti, Stati, Giorni} binary;
#Variabile binaria che vale 1 se la macchina 
#ha lavorato ad un qualsiasi prodotto il giorno g 0 altrimenti
var k{Stati, Giorni} binary;

#Funzione obbiettivo
maximize profitto: sum{p in Prodotti} v[p]*y[p,last(Stati),last(Giorni)]
-sum{m in Stati, p in Prodotti, g in Giorni} c[m]*x[p,m,g]
-sum{p in Prodotti}penale[p]*ma[p]
;

#Attivazione della variabile Y  per ogni 
#elemento di Giorni e Stati con ordine maggiore di 1
s.t. attivazioneY
{p in Prodotti, g in Giorni, s in Stati: ord(s)>1 and ord(g)>1}:
y[p,s,g]=y[p,s,prev(g)]+po[p,prev(s)]*x[p,prev(s),g]
-po[p,s]*x[p,s,g];

#Attivazione della variabile Y con 
#elementi di Giorni e stati con ordine uguale ad 1
s.t. attivazioneYS0G0{p in Prodotti}:
y[p,first(Stati),first(Giorni)]=startingUnits[p]
-po[p,first(Stati)]*x[p,first(Stati),first(Giorni)];

#Attivazione della variabile y con 
#l'elemento di Stati con ordine uguale ad 1
s.t. attivazioneYS0{p in Prodotti, g in Giorni:ord(g)>1}:
y[p,first(Stati),g]=y[p,first(Stati),prev(g)]
-po[p,first(Stati)]*x[p,first(Stati),g];

#Attivazione della variabile y con l'elemento 
#di Giorni con ordine uguale ad 
#1 e quello di stati con ordine uguale a 2
s.t. attivazioneYGOS2{p in Prodotti}:
y[p,member(2,Stati),first(Giorni)]=
po[p,first(Stati)]*x[p,first(Stati),first(Giorni)];

#Attivazione della variabile y con l'elemento di Giorni 
#con ordine uguale ad 1 e quello di stati 
#con ordine uguale maggiore a 2
s.t. attivazioneYGO{p in Prodotti, s in Stati:ord(s)>2}:
y[p,s,first(Giorni)]=0;

#Il numero di prodotti lavorati non puo' superare il numero di 
#prodotti che si aveva il giorno prima nello stato precedente
s.t. maxLav{p in Prodotti, g in Giorni, s in Stati:ord(s)>1 and ord(g)>1}: 
y[p,s,g]<=y[p,prev(s),prev(g)]; 

#Definizione della regola precedente ma nel caso 
#in cui si utilizza l'elemento di giorni con cardinalita' 
#pari ad 1 e di Stati con cardinalita' pari a 2
s.t. maxLavYGOS2{p in Prodotti}:
y[p,member(2,Stati),first(Giorni)]<=y[p,first(Stati),first(Giorni)];

#Attivazione della variabile Ma
s.t. attivazioneMa{p in Prodotti}:
y[p,last(Stati), last(Giorni)]+ma[p]>=minUnit[p];

#Attivazione della variabileZ
s.t. attivazioneZ{p in Prodotti, g in Giorni, m in Stati}:
x[p,m,g] <=z[p,m,g]*M;

#Attivazione della variabile K
s.t. attivazioneK{g in Giorni, m in Stati}:
sum{p in Prodotti}x[p,m,g]<=k[m,g]*M;

#Numero massimo di ore in cui la macchina puo' essere attiva
s.t. maxOre{g in Giorni, m in Stati}:
sum{p in Prodotti} x[p,m,g]+sum{p in Prodotti}z[p,m,g]-k[m,g]<=o;