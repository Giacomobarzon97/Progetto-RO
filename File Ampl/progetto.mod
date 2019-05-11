set Prodotti;
set Giorni ordered;
set Stati ordered;

#Dichiarazione Parametri
param v{Prodotti};
param c{Stati};
param po{Prodotti, Stati};
param minUnit{Prodotti};
param penale{Prodotti};
param startingUnits{Prodotti};
param o;

param M=8;

#Dichiarazione Variabili
var x{Prodotti, Stati, Giorni}>=0;
var y{Prodotti, Stati, Giorni}>=0 integer;
var ma{Prodotti}>=0 integer;
var z{Prodotti, Stati, Giorni} binary;
var k{Stati, Giorni} binary;

#Funzione obbiettivo
maximize profitto: sum{p1 in Prodotti} v[p1]*y[p1,last(Stati),last(Giorni)]
-sum{m1 in Stati} (c[m1]*sum{p2 in Prodotti, g in Giorni} x[p2,m1,g])
-sum{p3 in Prodotti}penale[p3]*ma[p3]
;

s.t. attivazioneY{p in Prodotti, g in Giorni, s in Stati: ord(s)>1 and ord(g)>1}:
y[p,s,g]=y[p,s,prev(g)]+po[p,prev(s)]*x[p,prev(s),g]-po[p,s]*x[p,s,g];

s.t. attivazioneYS0G0{p in Prodotti}:
y[p,first(Stati),first(Giorni)]=startingUnits[p]-po[p,first(Stati)]*x[p,first(Stati),first(Giorni)];

s.t. attivazioneYS0{p in Prodotti, g in Giorni:ord(g)>1}:
y[p,first(Stati),g]=y[p,first(Stati),prev(g)]-po[p,first(Stati)]*x[p,first(Stati),g];

s.t. attivazioneYGOS2{p in Prodotti}:
y[p,member(2,Stati),first(Giorni)]=po[p,first(Stati)]*x[p,first(Stati),first(Giorni)];

s.t. attivazioneYGO{p in Prodotti, s in Stati:ord(s)>2}:
y[p,s,first(Giorni)]=0;

s.t. maxLav{p in Prodotti, g in Giorni, s in Stati:ord(s)>1 and ord(g)>1}: 
y[p,s,g]<=y[p,prev(s),prev(g)]; 

s.t. maxLavYGOS2{p in Prodotti}:
y[p,member(2,Stati),first(Giorni)]<=y[p,first(Stati),first(Giorni)];

s.t. attivazioneMa{p in Prodotti}:
y[p,last(Stati), last(Giorni)]+ma[p]>=minUnit[p];

s.t. attivazioneZ{p in Prodotti, g in Giorni, m in Stati}:
x[p,m,g] <=z[p,m,g]*M;

s.t. attivazioneK{g in Giorni, m in Stati}:
sum{p in Prodotti}x[p,m,g]<=k[m,g]*M;

s.t. maxOre{g in Giorni, m in Stati}:
sum{p in Prodotti} x[p,m,g]+sum{p in Prodotti}z[p,m,g]-k[m,g]<=o;


