#install.packages("RJSONIO")
#install.packages("geosphere")
#install.packages("igraph")
#install.packages("lpSolveAPI")
#install.packages("GGally")
#install.packages("network")
#install.packages("sna")
#install.packages("ggplot2")

library(RJSONIO)
library(geosphere)
library(igraph)
library(lpSolveAPI)
library(GGally)

locations <- fromJSON("~/locations.json")
locations <- lapply(locations, function(x) {
  unlist(x)
})
locations <- as.data.frame(locations)
locations <- data.frame(locations[,2],locations[,1])

pair_d <- apply(locations, 1, FUN=function(X) distHaversine(X, locations))

n = nrow(pair_d)
d=1000
potential_matches <- ifelse(pair_d != 0 & pair_d <= d,1,0)

gr <- graph.adjacency(potential_matches, mode="undirected")
gr <- set_vertex_attr(gr,"name", value = seq(1,length(V(gr))))
degree_0 = V(gr)[degree(gr)==0]

gr = gr - degree_0

comp = decompose(gr)
ncomp = length(comp)

l = 0
matched_pairs = data.frame()
for (i in 1:ncomp){
  g = comp[[i]]
  lprec <- make.lp(0, length(E(g)))
  set.type(lprec,seq(1,length(E(g)),1), type ="binary")
  set.objfn(lprec, rep(-1,length(E(g))))
  vertices = unique(c(get.edgelist(g)[,1],get.edgelist(g)[,2]))
  for (v in vertices){
    e = rep(0,length(E(g)))
    e[get.edgelist(g)[,1]==v]=1
    e[get.edgelist(g)[,2]==v]=1
    add.constraint(lprec,e, "<=", 1)
  }
  solve(lprec)
  obj = - get.objective(lprec)
  matched_pairs = as.matrix(rbind(matched_pairs,get.edgelist(g)[get.variables(lprec)==1,]))
  l = l + 2*obj
}
matched_users = unique(c(matched_pairs[,1],matched_pairs[,2]))

print (paste("The number of matched users for 1000 meters threshold is:",l))

#vizualise matched pairs

library(network)
suppressWarnings(suppressMessages(library(sna)))
library(ggplot2)

adj = matrix(0, n, n)
adj[matched_pairs] <- 1
net = network(adj, directed = FALSE)
net = network(net, directed = FALSE)
net %v% "color" = ifelse((seq(1,100) %in% matched_pairs[,1]) | (seq(1,100) %in% matched_pairs[,2]), "tomato", "steelblue")
x = as.matrix(cbind(seq(1,100),seq(1,100)))
#x=gplot.layout.fruchtermanreingold(net, NULL)
net %v% "x" = ifelse(seq(1,100) %in% matched_pairs[,1], 1, 2)
net %v% "y" = seq(1,100,2)
ggnet2(net, mode = c("x", "y"), color = "color", node.size = 6, label.size = 3.5, edge.size = 1, edge.color = "grey", label = TRUE, layout.par = list(niter = 500))

#vizualise matched users

new_adj = matrix(1, n, n)
diag(new_adj) = 0
new_net = network(potential_matches, directed = FALSE)
new_net = network(new_net, directed = FALSE)
new_net %v% "color" = ifelse(seq(1,100) %in% matched_pairs[,1] | seq(1,100) %in% matched_pairs[,2], "tomato", "steelblue")
ggnet2(new_net, color = "color", node.size = 7, edge.size = 1, edge.color = "grey", label = FALSE, layout.par = list(niter = 500))

detach("package:sna", unload=TRUE)
######

n_matched <- function(d,pair_d){
  
  n = nrow(pair_d)
  potential_matches <- ifelse(pair_d != 0 & pair_d <= d,1,0)
  
  gr <- graph.adjacency(potential_matches, mode="undirected")
  gr <- set_vertex_attr(gr,"name", value = seq(1,length(V(gr))))
  degree_0 = V(gr)[degree(gr)==0]
  
  gr = gr - degree_0
  
  comp = decompose(gr)
  ncomp = length(comp)
  
  l = 0
  for (i in 1:ncomp){
    g = comp[[i]]
    lprec <- make.lp(0, length(E(g)))
    set.type(lprec,seq(1,length(E(g)),1), type ="binary")
    set.objfn(lprec, rep(-1,length(E(g))))
    vertices = unique(c(get.edgelist(g)[,1],get.edgelist(g)[,2]))
    for (v in vertices){
      e = rep(0,length(E(g)))
      e[get.edgelist(g)[,1]==v]=1
      e[get.edgelist(g)[,2]==v]=1
      add.constraint(lprec,e, "<=", 1)
    }
    solve(lprec)
    obj = - get.objective(lprec)
    l = l + 2*obj
  }
  
  return (l)
}

#first attempt at perfect matching

perfect_matching <- function(d){
  potential_matches <- ifelse(pair_d != 0 & pair_d <= d,1,0)
  n = nrow(pair_d)
  g <- graph.adjacency(potential_matches, mode="undirected")
  g <- set_vertex_attr(g,"name", value = seq(1,length(V(g))))
  degree_0 = V(g)[degree(g)==0]
  if (length(V(g)) != length(V(g-degree_0))){
    return (FALSE)
  }else{
    vertices = unique(c(get.edgelist(g)[,1],get.edgelist(g)[,2]))
    for (i in 1:(length(vertices)-1)){
      for (u in combn(vertices, (length(vertices)-i) , simplify = FALSE)){
        g_u = delete_vertices(g,u)
        l = 0
        ncomponents = length(decompose(g_u))
        if (ncomponents ==1){
          l = 1
        }else {
          for (j in 1:ncomponents){
            l = l + ifelse(length(V(decompose(g_u)[[j]]))%%2==1,1,0)
          }
        }
        if (l>length(u)){
          return (FALSE)
        }
      }
      print(i)
    }
  }
  return (TRUE)
}

# perfect matching using Tutte's Theorem

rdu<-function(n,k) sample(1:k,n,replace=T)

perfect_matching_tutte <- function(d){
  potential_matches <- ifelse(pair_d != 0 & pair_d <= d,1,0)
  n = nrow(pair_d)
  g <- graph.adjacency(potential_matches, mode="undirected")
  g <- set_vertex_attr(g,"name", value = seq(1,length(V(g))))
  degree_0 = V(g)[degree(g)==0]
  if (length(V(g)) != length(V(g-degree_0))){
    return (FALSE)
  }else{
    Tutte = matrix(0,nrow=n,ncol=n)
    for (i in 1:n){
      for (j in 1:n){
        if (are.connected(g,i,j)){
          Tutte[i,j]=ifelse(i>j,rdu(1,n^2),-rdu(1,n^2))
        }
      }
    }
    if (det(Tutte)!=0){
      return (TRUE)
    }
  }
  return (FALSE)
}

#binary search

distances = unique(sort(pair_d))
distances = unique(subset(distances, distances>1000))

which.median <- function(x) which.min(abs(x - median(x)))

L = which.min(distances)
R = which.max(distances)
m = which.median(distances[L:R])

L = 1
R = length(distances)
m = which.median(distances[L:R])
ptm <- proc.time()
while (R-L>0){
  if (!(perfect_matching_tutte(distances[m]))){
    L = m+1
    m = m + which.median(distances[L:R])
  }else{
    R = m-1
    m = L + which.median(distances[L:R])
  }
}

t = proc.time() - ptm
min_dist = distances[m]
print (paste("The minimum distance threshold for all users to be matched is:",round(min_dist,3),"meters"))
print (paste("The elapsed time for finding the minimum distance is:",round(t[3],3),"seconds"))

## Double-checking

#n_matched(distances[(m-1)],pair_d)<100
#c=0
#for (i in 1:100){
#  c= c+perfect_matching_tutte(distances[m])
#}
#c==100
