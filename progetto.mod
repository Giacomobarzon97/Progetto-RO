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

param M=2147483647;

#Dichiarazione Variabili
var x{Prodotti, Stati, Giorni}>=0;
var y{Prodotti, Stati, Giorni}>=0 integer;
var ma{Prodotti}>=0 integer;
var z{Prodotti, Stati, Giorni} binary;
var k{Stati, Giorni} binary;

#Funzione obbiettivo
maximize profitto: sum{p1 in Prodotti} v[p1]*y[p1,last(Stati),last(Giorni)]
-sum{m1 in Stati:ord(m1)>1} (c[m1]*sum{p2 in Prodotti, g in Giorni} x[p2,m1,g])
-sum{p3 in Prodotti}penale[p3]*ma[p3];

s.t. attivazioneY{p in Prodotti, g in Giorni, s in Stati: ord(s)>1 and ord(g)>1}:
y[p,s,g]=y[p,s,prev(g)]+po[p,prev(s)]*x[p,prev(s),g]-po[p,s]*x[p,s,g];

s.t. attivazioneYS0G0{p in Prodotti, g in Giorni}:
y[p,first(Stati),first(Giorni)]=startingUnits[p]-sum{s in Stati:ord(s)>1}po[p,s]*x[p,s,first(Giorni)];

s.t. attivazioneYS0{p in Prodotti, g in Giorni:ord(g)>1}:
y[p,first(Stati),g]=y[p,first(Stati),prev(g)]-sum{s in Stati:ord(s)>1}po[p,s]*x[p,s,prev(g)];

s.t. attivazioneYS2G0{p in Prodotti, g in Giorni, s in Stati:ord(s)=2}:
y[p,s,first(Giorni)]=po[p,s]*x[p,s,first(Giorni)];

s.t. attivazioneYG0{p in Prodotti, g in Giorni, s in Stati:ord(s)>2}:
y[p,s,first(Giorni)]=0;

s.t. maxLav{p in Prodotti, g in Giorni, s in Stati:ord(s)>1 and ord(g)>1}: 
y[p,s,g]<=y[p,prev(s),prev(g)]; 


s.t. attivazioneZ{p in Prodotti, g in Giorni, m in Stati:ord(m)>1}:
x[p,m,g]<=z[p,m,g]*M;

s.t. attivazioneK{p in Prodotti,g in Giorni,m in Stati:ord(m)>1}:
sum{p1 in Prodotti}x[p1,m,g]<=z[p,m,g]*M;

s.t. attivazioneMa{p in Prodotti}:
y[p,last(Stati), last(Giorni)]+ma[p]>=minUnit[p];

s.t. maxOre{g in Giorni, m in Stati:ord(m)>1}:
sum{p in Prodotti} x[p,m,g]+sum{p in Prodotti} z[p,m,g]-k[m,g]<=o;