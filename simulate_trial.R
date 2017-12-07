# August 29th, 2017
# Supplementary Material to accompany "Competing effects of indirect 
# protection and clustering on the power of cluster-randomized 
# controlled vaccine trials"

# Script to simulate an individually-randomized and cluster-randomized
# trial a given number of times, and return vaccine effect estimate and
# estimated power for a given set of parameters
# Also contains code to run the sample size calculations based on final
# size equations

# Number of simulated trials
nsim<-500

# Population structure parameters:
# Average size of one community
ave_community_size<-100
# Range of community sizes (sizes are uniformly distributed on this range)
community_size_range<-40
# Number of communities
num_communities<-80
# Probability of an edge between two nodes in the same community
rate_within<-0.15
# Probability of an edge between two nodes in different communities
rate_between<-0

# Disease characteristics:
# Per-time-step hazard of infection for a susceptible nodes from an infectious
# neighbour
beta<-0.01
# Expected number of importations to the population over two years
num_introductions<-50
# Leaky multiplicative efficacy of vaccine
direct_VE<-0.6
# Gamma-distribution parameters of incubation and infectious period
incperiod_shape<-3.11
incperiod_rate<-0.32
infperiod_shape<-1.13
infperiod_rate<-0.226
ave_inc_period <- ceiling(incperiod_shape/incperiod_rate)
# First day of trial enrollment, relative to start of epidemic
trial_startday<-150
# Days of follow-up
trial_length<-140
# Number of clusters targeted for enrollment
# Must be less than or equal to the number of communities
num_clusters_enrolled_per_day<-80
if (num_clusters_enrolled_per_day > num_communities) {stop("Enrolling too many communities!")}
# Number of days over which subjects are enrolled
enrollment_period<-1
# Target community enrollment proportion
cluster_coverage<-0.5

# Calculate R0
R0 <- (1 - (infperiod_rate/(infperiod_rate+beta))^infperiod_shape) *
  (((ave_community_size-1)*(1-rate_within)*rate_within + 
      (num_communities-1)*ave_community_size*(1-rate_between)*rate_between + 
      ((ave_community_size-1)*rate_within + (num_communities-1)*ave_community_size*rate_between)^2)/
     ((ave_community_size-1)*rate_within + (num_communities-1)*ave_community_size*rate_between)-1)
cat("R0: ",R0,"\n")
cat("Average number of individuals enrolled: ",num_clusters_enrolled_per_day*enrollment_period*cluster_coverage*ave_community_size)

list <- structure(NA,class="result")
"[<-.result" <- function(x,...,value) {
  args <- as.list(match.call())
  args <- args[-c(1:2,length(args))]
  length(value) <- length(args)
  for(i in seq(along=args)) {
    a <- args[[i]]
    if(!missing(a)) eval.parent(substitute(a <- v,list(a=a,v=value[[i]])))
  }
  x
}

make_network <- function(ave_community_size, community_size_range, 
                         num_communities, rate_within, rate_between) {
  # Function to make a network of closely-connected communities that are more sparsely
  # connected with each other. I use a stochastic block model.
  # Inputs:
  # Ave_community_size is the average number of people in a community
  # Community_size_range is the range of community sizes. Currently size of a community
  # is being chosen from a uniform distribution on (ave-range/2, ave+range/2)
  # Num_communities is the number of communities in the study population
  # rate_within is the probability of an edge between any two nodes within the same community
  # rate_between is the probability of an edge between any two nodes in different communities
  
  require(NetSurv)
  require(Matrix)
  require(Rlab)
  require(igraph)
  require(deSolve)
  require(reshape2)
  require(ggplot2)
  
  # Create the network, and assign all members a community number
  # The community number will be output by the epidemic function and used in the 
  # gamma frailty model and calculation of the ICC
  community_sizes <- ave_community_size + round(runif(num_communities,-community_size_range/2,community_size_range/2))
  studypop_size <- sum(community_sizes)
  # All communities have the same connectedness, and all communities are equally
  # connected to each other
  within_rates <- diag(nrow=num_communities,ncol=num_communities,x=rate_within)
  between_rates <- matrix(rate_between,nrow=num_communities,ncol=num_communities) -
    diag(nrow=num_communities,ncol=num_communities,x=rate_between)
  rates<-within_rates+between_rates
  g <- sample_sbm(studypop_size,rates,community_sizes)
  # Give the nodes a name so that igraph remembers them
  V(g)$name<-1:studypop_size
  V(g)$community<-rep(1:num_communities,community_sizes)
  # Trial status will track whether a node is not in the trial (NA), in the control arm (0) or
  # in the vaccine arm (1)
  V(g)$trialstatus<-NA
  V(g)$enrollmentday<-NA
  
  return(g)
  
}

network_epidemic<-function(g,beta,num_introductions,VE,
                           incperiod_shape,incperiod_rate,infperiod_shape,infperiod_rate,
                           bTrial,bCluster,
                           trial_startday,trial_length,
                           num_enrolled_per_day,enrollment_period,cluster_coverage,simnum) {
  # Inputs:
  # g - the graph to run the epidemic on
  # beta - Every infectious individual contacts all their neighbours in a time step
  # and infects each susceptible with hazard beta. So beta represents the hazard of infection from one
  # contact between an infectious and a susceptible.
  # num_introductions - how many separate introductions we expect on average from the main epidemic. This is used
  # to calibrate the external force of infection
  # VE - direct leaky efficacy of the vaccine
  # bTrial - whether we are running a trial or not
  # bCluster - indicator of whether we are running the cRCT (1) or the iRCT (0)
  # trial_startday - first day of trial enrollment
  # trial_length - end of follow-up of trial partcipants, counting from the first day of enrollment
  # num_enrolled_per_day - number of individuals/clusters enrolled per day
  # enrollment_period - length of enrollment period
  # cluster_coverage - The proportion of each cluster we expect to enroll
  
  require(NetSurv)
  require(Matrix)
  require(Rlab)
  require(igraph)
  require(deSolve)
  require(reshape2)
  require(ggplot2)
  require(caTools)
  
  list <- structure(NA,class="result")
  "[<-.result" <- function(x,...,value) {
    args <- as.list(match.call())
    args <- args[-c(1:2,length(args))]
    length(value) <- length(args)
    for(i in seq(along=args)) {
      a <- args[[i]]
      if(!missing(a)) eval.parent(substitute(a <- v,list(a=a,v=value[[i]])))
    }
    x
  }
  
  # Recover and spread functions
  recover<-function(e_nodes,i_nodes,r_nodes,infperiod_shape,infperiod_rate) {
    # Input is a list of the exposed nodes, 
    # with number of days since infection and total incubation/latent
    # period, and equivalently for the infectious nodes.
    # For each of these nodes, we will add it to newinfectious if the number of days exposed has
    # reached the total length of the incubation period, and equivalently for the infectious nodes.
    
    # Advance infectious nodes first, otherwise you will doubly advance any nodes switching from
    # exposed to infectious at this time step
    indices_to_remove <- i_nodes[2,]>=i_nodes[3,]
    newremoved<-as.vector(i_nodes[1,indices_to_remove])
    
    # Add one day to the length of each infected individual's time infected
    i_nodes[2,] <- i_nodes[2,]+1
    
    # Remove any recovered from i_nodes and add to r_nodes
    i_nodes <- i_nodes[,!(i_nodes[1,] %in% newremoved),drop=FALSE]
    r_nodes <- c(r_nodes,newremoved)
    
    # Now advance exposed nodes
    indices_to_remove <- e_nodes[2,]>=e_nodes[3,]
    newinfectious<-as.vector(e_nodes[1,indices_to_remove])
    
    # Add one day to the length of each infected individual's time infected
    e_nodes[2,] <- e_nodes[2,]+1
    
    # Remove any progressing from e_nodes and add to i_nodes
    e_nodes <- e_nodes[,!(e_nodes[1,] %in% newinfectious),drop=FALSE]
    inf_periods <- rgamma(length(newinfectious),infperiod_shape,infperiod_rate)
    i_nodes <- cbind(i_nodes,rbind(newinfectious,rep(0,length(newinfectious)),inf_periods))
    
    list(e_nodes, i_nodes, r_nodes, sort(newinfectious))
  }
  
  spread<-function(g, s_nodes, v_nodes, e_nodes, i_nodes, beta, VE,
                   incperiod_shape, incperiod_rate,
                   connected_nodes,external_inf_F,source_num_inf){
    # Spread will create new infected nodes from two sources: infectious nodes within the the study
    # population, and external pressure from the source population
    # Inputs:
    # g is the graph, used to find neighbours of infected nodes
    # s_nodes, e_nodes and i_nodes are susceptible, exposed and infected nodes
    # beta is the hazard of infection for one contact
    # incperiod_shape and rate are used to assign each newly exposed node a latent/incubation period
    # length, currently drawn from a gamma distribution
    # connected_nodes is a list of nodes that are connected the the source population
    # external_inf_F is a constant of proportionality that defines infectious pressure from source population 
    # to an individual
    # source_num_inf is the number of infectious individuals in the source population
    
    # Process: go through list of i_nodes, and choose a random number of its susceptible neighbours to
    # be infected, according to beta and choose a random number of its susceptible vaccinated neighbours to
    # be infected, according to beta and VE
    # Then go through list of nodes that are connected to source population and infect each susceptible
    # one with probability 1-exp(-FI), where I is the number/proportion of infectious, and F is a constant
    
    if (ncol(i_nodes)>0) {
      
      # Make a beta vector
      betavec <- rep(beta,ncol(i_nodes))
      beta_v <- betavec*(1-VE)
      
      # Get a list of all neighbours of all infected nodes
      potential_contacts<-lapply(i_nodes[1,],function(x) neighbors(g,x))
      susc_contacts<-lapply(potential_contacts,function(x,susceptibles) intersect(x,susceptibles),susceptibles=s_nodes)
      num_neighbours_susc<-rapply(susc_contacts,length)
      # Sample from each group of neighbours in turn
      # First choose how many neighbours each node infects
      num_contacts_susc<-rbinom(length(num_neighbours_susc),num_neighbours_susc,1-exp(-betavec))
      # Then sample from the neighbours
      # If one node gets picked twice by different nodes, just discard the duplicate.
      # In the very rare case that each i_nodes makes a number of new infectees equal to the number
      # of infectious nodes, mapply will make a matrix and unlist won't work. Therefore, the c() around
      # it ensures we turn the matrix into a vector. Unique then removes duplicates.
      infectees_susc<-c(unlist(mapply(function(x,y) x[sample.int(length(x),y)],x=susc_contacts,y=num_contacts_susc)))
      infectees_susc<-unique(infectees_susc)
      
      if (length(v_nodes)>0) {
        # Same as above but with vaccinated susceptible nodes
        vacc_contacts<-lapply(potential_contacts,function(x,vacc) intersect(x,vacc),vacc=v_nodes)
        num_neighbours_vacc<-rapply(vacc_contacts,length)
        num_contacts_vacc<-rbinom(length(num_neighbours_vacc),num_neighbours_vacc,1-exp(-beta_v))
        infectees_vacc<-c(unlist(mapply(function(x,y) x[sample.int(length(x),y)],x=vacc_contacts,y=num_contacts_vacc)))
        infectees_vacc<-unique(infectees_vacc)
      } else {
        infectees_vacc<-c()
      }
      
      infectees <- c(infectees_susc, infectees_vacc)
      
    } else {
      infectees_susc <- c()
      infectees_vacc <- c()
      infectees <- c()
    }
    # Pick out the nodes connected to the source that are still susceptible 
    # and haven't just been infected
    target_cnodes_susc <- setdiff(intersect(connected_nodes,s_nodes),infectees_susc)
    target_cnodes_vacc <- setdiff(intersect(connected_nodes,v_nodes),infectees_vacc)
    
    # Make a vector to represent external infection hazard for each individual
    communities_s <- V(g)[target_cnodes_susc]$community
    communities_v <- V(g)[target_cnodes_vacc]$community
    comm_sizes_s <- sapply(1:num_communities,function(x) sum(communities_s==x))
    comm_sizes_v <- sapply(1:num_communities,function(x) sum(communities_v==x))
    
    # Hazard of infection
    extFs_s<-rep(extF,comm_sizes_s)
    extFs_v<-rep(extF,comm_sizes_v)
    
    # Probability of infection
    prob_inf_fromsource <- 1 - exp(-mean(extFs_s)*source_num_inf)
    prob_inf_fromsource_v <- 1 - exp(-(1-VE)*mean(extFs_v)*source_num_inf)
    
    # Choose a number of individuals to be infected, then sample those individuals
    if (length(target_cnodes_susc)>0) {
      num_conn_inf_susc <- rbinom(1,length(target_cnodes_susc),prob_inf_fromsource)
      conn_inf_susc <- target_cnodes_susc[sample.int(length(target_cnodes_susc),num_conn_inf_susc,prob=extFs_s)]
    } else {
      conn_inf_susc <- c()
    }
    
    # Same as above, but for vaccinated individuals
    if (length(target_cnodes_vacc)>0) {
      num_conn_inf_vacc <- rbinom(1,length(target_cnodes_vacc),prob_inf_fromsource_v)
      conn_inf_vacc <- target_cnodes_vacc[sample.int(length(target_cnodes_vacc),num_conn_inf_vacc,prob=extFs_v)]
    } else {
      conn_inf_vacc <- c()
    }
    
    newinfected_susc <- c(infectees_susc,conn_inf_susc)
    newinfected_vacc <- c(infectees_vacc,conn_inf_vacc)
    newinfected <- c(newinfected_susc, newinfected_vacc)
    newinfected <- unique(newinfected)
    
    if (length(newinfected)>0) {
      
      # Give each newly exposed node an incubation/latent period
      inc_periods <- rgamma(length(newinfected),incperiod_shape,incperiod_rate)
      # Add them to e_nodes and remove from s_nodes and v_nodes
      e_nodes <- cbind(e_nodes,rbind(newinfected,rep(0,length(newinfected)),inc_periods))
      s_nodes<-setdiff(s_nodes,newinfected_susc)
      v_nodes <- setdiff(v_nodes,newinfected_vacc)
      
    }
    
    list(s_nodes, v_nodes, e_nodes)
  }
  
  #### RUN THE EPIDEMIC IN THE SOURCE POPULATION ####
  # This is to define external infectious pressure to the network
  
  model <- function(t, y, parms) {
    with(as.list(c(y,parms)), {
      
      beta <- betahat * (1 - a2/(1 + exp(-a1 * (t - atau))))
      
      dS <- -beta * S * (I1+I2+I3) / (S+E1+E2+E3+I1+I2+I3+R)
      dE1 <- beta * S * (I1+I2+I3) / (S+E1+E2+E3+I1+I2+I3+R) - sigma * 3 * E1
      dE2 <- sigma * 3 * E1 - sigma * 3 * E2
      dE3 <- sigma * 3 * E2 - sigma * 3 * E3
      dI1 <- sigma * 3 * E3 - gamma * 3 * I1
      dI2 <- gamma * 3 * I1 - gamma * 3 * I2
      dI3 <- gamma * 3 * I2 - gamma * 3 * I3
      dR <- gamma * 3 * I3
      list(c(dS,dE1,dE2,dE3,dI1,dI2,dI3,dR))
    })
  }
  N <- 50000
  y<- c(S=N-1,E1=0,E2=0,E3=0,I1=1,I2=0,I3=0,R=0)
  times<-seq(0,730,1)
  parms<-c(betahat=0.94,a1=0.19,a2=0.6,atau=27.79,sigma=0.14,gamma=0.33)
  out<-as.data.frame(lsoda(y,times,model,parms))
  
  #### RUN THE EPIDEMIC IN THE STUDY POPULATION ####
  
  # Define how the study population is linked to the source population
  # Connect all individuals to source population at same hazard
  # Constant of proportionality varies by community
  studypop_size<-length(V(g))
  connected_to_source <- V(g)$name
  
  # Calibrate extF to the number of introductions, given the progression of the epidemic in the source population
  num_communities <- max(V(g)$community)
  comm_sizes <- sapply(1:num_communities,function(x) length(V(g)[community==x]))
  sumsqrt <- sum(sqrt(comm_sizes))
  extF <- -log(1-num_introductions/(sqrt(comm_sizes)*sumsqrt))/trapz(times,out$I1+out$I2+out$I3)
  
  # Number of timesteps to run the epidemic - only need to go until the end of the trial
  num_timesteps <- trial_startday + trial_length + enrollment_period - 1
  
  if (bTrial) {
    
    # Parameters to do with trial recruitment
    # Enrollment per day is number of clusters enrolled per day
    enrollment_schedule <- rep(num_enrolled_per_day,enrollment_period)
    enroll_endday <- trial_startday+enrollment_period-1
    
    non_trial_clusters <- 1:max(V(g)$community)
    
  }
  
  # Initialize the S, E, I, and R nodes. I seed the epidemic from an SIR curve in a source population,
  # so initially all nodes in the study population are susceptible
  # i_nodes and e_nodes are matrices. The first row is the  identity of the node. The second row
  # is the number of days since infection/infectiousness. The third row is the total incubation/infectious period, 
  # drawn from a distribution when it becomes infected/infectious.
  # We are only going to consider a vaccine with effects on susceptibility, so only need one
  # vaccinated class
  e_nodes<-matrix(nrow=3,ncol=0)
  i_nodes<-matrix(nrow=3,ncol=0)
  v_nodes<-c()
  s_nodes <- as.vector(V(g))
  r_nodes <- c()
  
  # Initialize results.
  # Results will be, for each newly-infected node, the identity of the node, the day it was infected,
  # the community of which it is a member and its trial status at the time of infection. 
  # This is enough information to run a Cox PH with gamma frailty.
  # Make a data frame the size of the study pop and fill it in, then trim at the end
  results<-data.frame("SimulationNumber"=rep(NA,studypop_size),
                      "InfectedNode"=rep(NA,studypop_size),
                      "DayInfected"=rep(NA,studypop_size),
                      "Community"=rep(NA,studypop_size),
                      "TrialStatus"=rep(NA,studypop_size),
                      "DayEnrolled"=rep(NA,studypop_size))
  numinfectious<-0
  
  for (t in 1:num_timesteps) {
    
    # I'm recovering first, so I need to ensure that everyone has at least one chance to infect.
    # I do this by initializing an infectious node with 0 days since infection, seeing whether they
    # recover, then advancing them one day along their infectious period.
    
    if (bTrial) {
      
      # Recruit and randomize if during the enrollment period
      if ((t>=trial_startday) && (t<=enroll_endday)) {
        
        num_to_enroll <- enrollment_schedule[t-trial_startday+1]
        
        if (bCluster == 0) {
          # Individually-randomized trial, stratifying on community
          
          # Need to choose from the clusters not already enrolled
          new_clusters <- sample(non_trial_clusters,num_to_enroll)
          
          # From the chosen clusters, choose a fraction of the non-infectious individual. That fraction is defined in the inputs
          # I will then vaccinate half of each chosen sample
          # For each new cluster, I sample from that cluster a proportion of the whole cluster,
          # but only from the susceptible or exposed individuals. If I'm trying to sample more than are available (because
          # there are lots of infectious/recovered individuals), just sample all of them.
          # These are the people who are recruited - I then assign half and half to vaccine or control
          new_recruits <- lapply(new_clusters,
                                 function(x) sample(intersect(V(g)[community==x]$name,c(e_nodes[1,],s_nodes)),
                                                    min(round(cluster_coverage*length(V(g)[community==x]$name)),
                                                        length(intersect(V(g)[community==x]$name,c(e_nodes[1,],s_nodes))))))
          new_vacc <- unlist(lapply(new_recruits,
                                    function(x) sample(x,round(length(x)/2))))
          new_controls <- setdiff(unlist(new_recruits),new_vacc)
          
          
          non_trial_clusters<-setdiff(non_trial_clusters,new_clusters)
          
        } else {
          
          # We try and enroll as many from the cluster as you can. I have set an
          # enrollment rate rather than cluster size, e.g. 70% enrolled in each cluster.
          # It means that every simulated trial would have slightly different numbers enrolled 
          # (=coverage*ave_community_size)
          
          # Need to choose from the clusters not already enrolled
          new_clusters <- sample(non_trial_clusters,num_to_enroll)
          new_clusters_v <- sample(new_clusters,num_to_enroll/2)
          new_clusters_c <- setdiff(new_clusters,new_clusters_v)
          # From the chosen clusters, a fraction of the non-infectious individual. That fraction is defined in the inputs
          # This looks complicated: for each new cluster, I sample from that cluster a proportion of the whole cluster,
          # but only from the susceptible or exposed individuals. If I'm trying to sample more than are available (because
          # there are lots of infectious/recovered individuals), just sample all of them.
          new_vacc <- unlist(lapply(new_clusters_v,
                                    function(x) sample(intersect(V(g)[community==x]$name,c(e_nodes[1,],s_nodes)),
                                                       min(round(cluster_coverage*length(V(g)[community==x]$name)),
                                                           length(intersect(V(g)[community==x]$name,c(e_nodes[1,],s_nodes)))))))
          new_controls <- unlist(lapply(new_clusters_c,
                                        function(x) sample(intersect(V(g)[community==x]$name,c(e_nodes[1,],s_nodes)),
                                                           min(round(cluster_coverage*length(V(g)[community==x]$name)),
                                                               length(intersect(V(g)[community==x]$name,c(e_nodes[1,],s_nodes)))))))
          
          non_trial_clusters<-setdiff(non_trial_clusters,new_clusters)
        }
        
        V(g)[name %in% new_controls]$trialstatus<-0
        V(g)[name %in% new_vacc]$trialstatus<-1
        V(g)[name %in% new_controls]$enrollmentday<-t
        V(g)[name %in% new_vacc]$enrollmentday<-t
        
        # Move the vaccinated susceptibles to from s_nodes to v_nodes
        vacc_susc <- intersect(s_nodes,new_vacc)
        s_nodes <- setdiff(s_nodes,vacc_susc)
        v_nodes <- c(v_nodes,vacc_susc)
        
      }
      
    }
    
    # Only need to recover if there are any infected or exposed
    if ((ncol(i_nodes)>0)||(ncol(e_nodes)>0)) {
      list[e_nodes,i_nodes,r_nodes,newinfectious]<-
        recover(e_nodes,i_nodes,r_nodes,infperiod_shape,infperiod_rate)
      
    } else {
      newinfectious <- c()
    }
    
    list[s_nodes,v_nodes,e_nodes]<-
      spread(g,s_nodes,v_nodes,e_nodes,i_nodes,
             beta,VE,incperiod_shape,incperiod_rate,
             connected_to_source,extF,out$I1[t]+out$I2[t]+out$I3[t])
    
    numnewinfectious<-length(newinfectious)
    if (numnewinfectious>0) {
      
      newcommunities <- V(g)[name %in% newinfectious]$community
      
      # Update results
      results$SimulationNumber[(numinfectious+1):(numinfectious+numnewinfectious)]<-rep(simnum,numnewinfectious)
      results$InfectedNode[(numinfectious+1):(numinfectious+numnewinfectious)]<-newinfectious
      results$DayInfected[(numinfectious+1):(numinfectious+numnewinfectious)]<-rep(t,numnewinfectious)
      results$Community[(numinfectious+1):(numinfectious+numnewinfectious)]<-newcommunities
      results$TrialStatus[(numinfectious+1):(numinfectious+numnewinfectious)]<-V(g)[name %in% newinfectious]$trialstatus
      results$DayEnrolled[(numinfectious+1):(numinfectious+numnewinfectious)]<-V(g)[name %in% newinfectious]$enrollmentday
      
      numinfectious <- numinfectious+numnewinfectious
      
    }
    
  }
  
  trial_nodes <- V(g)[!is.na(V(g)$trialstatus)]$name
  trial_nodes_info<-data.frame("SimulationNumber"=rep(simnum,length(trial_nodes)),
                               "Node"=trial_nodes,
                               "Community"=V(g)[trial_nodes]$community,
                               "TrialStatus"=V(g)[trial_nodes]$trialstatus,
                               "DayEnrolled"=V(g)[trial_nodes]$enrollmentday)
  
  # Tidy up results
  if (numinfectious>0) {
    results<-results[1:numinfectious,]
  } else {
    results<-results[1,]
    results$SimulationNumber[1]<-simnum
  }
  
  list(results,trial_nodes_info)
  
}

analyse_data <- function(results,trial_nodes,trial_startday,trial_length,ave_inc_period,
                         numclusters_perarm,bCluster) {
  
  library(survival)
  library(coxme)
  library(frailtypack)
  library(lme4)
  
  list <- structure(NA,class="result")
  "[<-.result" <- function(x,...,value) {
    args <- as.list(match.call())
    args <- args[-c(1:2,length(args))]
    length(value) <- length(args)
    for(i in seq(along=args)) {
      a <- args[[i]]
      if(!missing(a)) eval.parent(substitute(a <- v,list(a=a,v=value[[i]])))
    }
    x
  }
  
  coxmodel <- function(data,VEpointest) {
    
    survmodel<-try(coxph(Surv(DayInfected,eventstatus)~TrialStatus+strata(Community),data),silent=T)
    usesurvmod <- !inherits(survmodel, 'try-error')
    
    if (usesurvmod && vcov(survmodel)>=0){
      # If no error was thrown and the variance is positive, use the results of the model
      
      vaccEffEst <- 1-exp(survmodel$coefficient + c(0, 1.96, -1.96)*sqrt(survmodel$var))
      zval <- survmodel$coefficient/sqrt(survmodel$var)
      pval <- pnorm(zval, lower.tail = vaccEffEst[1]>0)*2
      
    } else {
      
      vaccEffEst<-c(VEpointest,NA,NA)
      pval <- NA
      
    }
    
    list(vaccEffEst,pval)
    
  }
  
  clustermodels <- function(data,VEpointest) {
    
    # Gaussian shared frailty, using coxme
    mod <- try(coxme(Surv(DayInfected, eventstatus) ~ TrialStatus + (1|Community), data = data),silent=T)
    usemod <- !inherits(mod, 'try-error')
    
    if (usemod && is.na(vcov(mod))) {
      vaccEffEst_gaussian_coxme <- c(VEpointest,NA,NA)
      pval_gaussian_coxme<-NA
    } else {
      if (usemod && vcov(mod)>=0){
        # If the model converges and variance is positive, use results of model
        
        vaccEffEst_gaussian_coxme <- 1-exp(mod$coefficients + c(0, 1.96, -1.96)*sqrt(vcov(mod)))
        zval <- mod$coefficients/sqrt(vcov(mod))
        pval_gaussian_coxme <- pnorm(zval, lower.tail = vaccEffEst_gaussian_coxme[1]>0)*2
      } else {
        vaccEffEst_gaussian_coxme <- c(VEpointest,NA,NA)
        pval_gaussian_coxme<-NA
      }
    }
    
    # Try with a gaussian-distributed random effect.
    mod2 <- try(coxph(Surv(DayInfected, eventstatus) ~ TrialStatus + frailty(Community,distribution="gaussian",sparse=FALSE), data = data), silent=T)
    usemod2 <- !inherits(mod2, 'try-error')
    
    if (usemod2 && is.na(vcov(mod2))) {
      vaccEffEst_gaussian_coxph <- c(VEpointest,NA,NA)
      pval_gaussian_coxph<-NA
    } else {
      if (usemod2 && vcov(mod2)>=0){
        
        vaccEffEst_gaussian_coxph <- 1-exp(mod2$coefficients[1] + c(0, 1.96, -1.96)*sqrt(vcov(mod2)[1]))
        zval2 <- mod2$coefficients[1]/sqrt(vcov(mod2)[1])
        pval_gaussian_coxph <- pnorm(zval2, lower.tail = vaccEffEst_gaussian_coxph[1]>0)*2
      } else {
        vaccEffEst_gaussian_coxph <- c(VEpointest,NA,NA)
        pval_gaussian_coxph<-NA
      }
    }
    
    # Try with a gamma-distributed random effect, using coxph and frailty
    mod3 <- try(coxph(Surv(DayInfected, eventstatus) ~ TrialStatus + frailty(Community,distribution="gamma",sparse=FALSE), data = data), silent=T)
    usemod3 <- !inherits(mod3, 'try-error')
    
    if (usemod3 && is.na(vcov(mod3))) {
      vaccEffEst_gamma_coxph <- c(VEpointest,NA,NA)
      pval_gamma_coxph<-NA
    } else {
      if (usemod3 && vcov(mod3)>=0){
        
        vaccEffEst_gamma_coxph <- 1-exp(mod3$coefficients[1] + c(0, 1.96, -1.96)*sqrt(vcov(mod3)[1]))
        zval3 <- mod3$coefficients[1]/sqrt(vcov(mod3)[1])
        pval_gamma_coxph <- pnorm(zval3, lower.tail = vaccEffEst_gamma_coxph[1]>0)*2
      } else {
        vaccEffEst_gamma_coxph <- c(VEpointest,NA,NA)
        pval_gamma_coxph<-NA
      }
    }
    
    # Generalized estimating equations/robust variance
    mod5 <- try(coxph(Surv(DayInfected, eventstatus) ~ TrialStatus + cluster(Community), data = data), silent=T)
    usemod5 <- !inherits(mod5, 'try-error')
    
    if (usemod5 && is.na(vcov(mod5))) {
      vaccEffEst_gee <- c(VEpointest,NA,NA)
      pval_gee<-NA
    } else {
      if (usemod5 && vcov(mod5)>=0){
        
        vaccEffEst_gee <- 1-exp(mod5$coefficients[1] + c(0, 1.96, -1.96)*sqrt(vcov(mod5)[1]))
        zval5 <- mod5$coefficients[1]/sqrt(vcov(mod5)[1])
        pval_gee <- pnorm(zval5, lower.tail = vaccEffEst_gee[1]>0)*2
      } else {
        vaccEffEst_gee <- c(VEpointest,NA,NA)
        pval_gee<-NA
      }
    }
    
    list(vaccEffEst_gaussian_coxme,pval_gaussian_coxme,
         vaccEffEst_gaussian_coxph,pval_gaussian_coxph,
         vaccEffEst_gamma_coxph,pval_gamma_coxph,
         vaccEffEst_gee,pval_gee)
    
  }
  
  results$DayInfected <- results$DayInfected - results$DayEnrolled
  
  # Get a list of nodes that were enrolled in the trial but never infected
  noninf<-setdiff(trial_nodes$Node,results$InfectedNode)
  # Get list of nodes that became infectious while they were in the trial
  # This is the step that excludes those who were R at time of enrollment
  results_analysis<-results[!is.na(results$TrialStatus),]
  # Get a list of nodes who were infected after their follow-up time was over
  # (i.e. those enrolled at the beginning but infected right at the end)
  censored <- results_analysis[results_analysis$DayInfected>trial_length,]
  results_analysis<-results_analysis[results_analysis$DayInfected<=trial_length,]
  # Assign them eventstatus=1 for the Cox analysis
  results_analysis$eventstatus<-rep(1,nrow(results_analysis))
  # Make data frame for those who were never infected (i.e. censored by end of study)
  noninfdf<-data.frame(InfectedNode=noninf,DayInfected=rep(trial_length,length(noninf)),
                       Community=trial_nodes$Community[trial_nodes$Node %in% noninf],
                       TrialStatus=trial_nodes$TrialStatus[trial_nodes$Node %in% noninf],
                       eventstatus=rep(0,length(noninf)),
                       DayEnrolled=trial_nodes$DayEnrolled[trial_nodes$Node %in% noninf])
  if (nrow(censored)>0) {
    censored$DayInfected<-trial_length
    censored$eventstatus<-0
  }
  # Remove column with simulation number so the columns match up
  results_analysis$SimulationNumber<-NULL
  results_analysis<-rbind(results_analysis,noninfdf,censored)
  
  # Finally, exclude any cases who were infected during the first n days of follow-up
  # This tries to rid of those who were already latently infected when enrolled
  results_analysis<-results_analysis[results_analysis$DayInfected>ave_inc_period,]
  
  numevents_vacc <- nrow(results_analysis[(results_analysis$eventstatus==1) & (results_analysis$TrialStatus==1),])
  numevents_cont <- nrow(results_analysis[(results_analysis$eventstatus==1) & (results_analysis$TrialStatus==0),])
  
  total_vacc_pt <- sum(results_analysis$DayInfected[results_analysis$TrialStatus==1])
  total_cont_pt <- sum(results_analysis$DayInfected[results_analysis$TrialStatus==0])
  VE_pointest <- 1 - (numevents_vacc/total_vacc_pt)/(numevents_cont/total_cont_pt)
  
  sample_size <- nrow(results_analysis)
  
  # Calculate ICC
  # Number of events in each cluster
  events_by_cluster<-aggregate(results_analysis$eventstatus,
                               by=list(Community=results_analysis$Community),FUN=sum)
  # Size of each cluster
  cluster_sizes<-aggregate(results_analysis$InfectedNode,by=list(Community=results_analysis$Community),FUN=length)
  # Overall trial size
  N <- sum(cluster_sizes$x)
  # Overall number of clusters
  K <- nrow(cluster_sizes)
  n0 <- 1/(K-1) * (N - sum(cluster_sizes$x^2)/N)
  n01 <- 1/(K-1) * ((K-1)*n0 - sum(cluster_sizes$x^2)/N)
  MSB <- 1/(K-1) * sum((events_by_cluster$x-mean(events_by_cluster$x))^2/cluster_sizes$x)
  MSW <- 1/(N-K-1) * sum(events_by_cluster$x-events_by_cluster$x^2/cluster_sizes$x)
  ICC <- (MSB - MSW) / (MSB + (n01-1) * MSW)
  deff <- 1+(mean(cluster_sizes$x)-1)*ICC
  
  # Proportion of clusters that have zero cases
  prop_zeros <- sum(events_by_cluster$x==0)/K
  
  if (bCluster == 0) {
    # Analysis for iRCT
    if ((numevents_vacc>0)&&(numevents_cont>0)) {
      # If we have events in both arms, can try a Cox PH. It can still be singular, so if it
      # throws an error, the trial has failed (not enough events)
      list[vaccEffEst,pval] <- coxmodel(results_analysis,VE_pointest)
      
    } else if ((numevents_vacc>0)&&(numevents_cont==0)) {
      # If there are no events in the control arm but
      # events in the vaccine arm, VE estimate is -1 and p-value is 1
      vaccEffEst<-c(-1,-1,-1)
      pval <- 1
      
    } else if ((numevents_vacc==0)&&(numevents_cont>0)) {
      # If there are no events in the vaccine arm and events in the control arm, VE is 1, but
      # for the p-value we add one event to both arms and do a Cox regression on that data
      # I give both events the median time among control events.
      newevent_v_rownum <- min(which((results_analysis$eventstatus==0)&(results_analysis$TrialStatus==1)))
      newevent_c_rownum <- min(which((results_analysis$eventstatus==0)&(results_analysis$TrialStatus==0)))
      
      eventtime <- median(results_analysis$DayInfected[results_analysis$eventstatus==1])
      
      results_analysis$DayInfected[newevent_v_rownum] <- eventtime
      results_analysis$eventstatus[newevent_v_rownum] <- 1
      
      results_analysis$DayInfected[newevent_c_rownum] <- eventtime
      results_analysis$eventstatus[newevent_c_rownum] <- 1
      
      list[,pval] <- coxmodel(results_analysis,VE_pointest)
      vaccEffEst<-1
      
    } else {
      # If no events are observed in either arm, the trial has failed and no result can be obtained
      vaccEffEst<-c(NA,NA,NA)
      pval <- NA
      
    }
    
    list(vaccEffEst,pval,numevents_vacc,numevents_cont,sample_size)
    
  } else {
    
    if ((numevents_vacc>0)&&(numevents_cont>0)) {
      # Run the models for the clustered data
      list[vaccEffEst_gaussian_coxme,pval_gaussian_coxme,
           vaccEffEst_gaussian_coxph,pval_gaussian_coxph,
           vaccEffEst_gamma_coxph,pval_gamma_coxph,
           vaccEffEst_gee,pval_gee] <- 
        clustermodels(results_analysis,VE_pointest)
      
    } else if ((numevents_vacc>0)&&(numevents_cont==0)) {
      # If there are no events in the control arm but
      # events in the vaccine arm, VE estimate is -1 and p-value is 1
      vaccEffEst_gaussian_coxme<-c(-1,-1,-1)
      pval_gaussian_coxme<-1
      vaccEffEst_gaussian_coxph<-c(-1,-1,-1)
      pval_gaussian_coxph<-1
      vaccEffEst_gamma_coxph<-c(-1,-1,-1)
      pval_gamma_coxph<-1
      vaccEffEst_gee<-c(-1,-1,-1)
      pval_gee<-1
      
    } else if ((numevents_vacc==0)&&(numevents_cont>0)) {
      # If there are no events in the vaccine arm and events in the control arm, VE is 1
      # For p-value, add one event to both arms. Give it the median event time among control events.
      # Cluster for event in vaccine arm doesn't matter
      # Choose cluster for event in control arm to be most conservative
      
      communities <- results_analysis$Community[((results_analysis$eventstatus==1)&(results_analysis$TrialStatus==0))]
      freq_table <- sort(table(communities),decreasing=TRUE)
      community <- as.numeric(names(freq_table[1]))
      
      newevent_v_rownum <- min(which((results_analysis$eventstatus==0)&(results_analysis$TrialStatus==1)))
      newevent_c_rownum <- min(which((results_analysis$eventstatus==0)&(results_analysis$TrialStatus==0)&(results_analysis$Community==community)))
      
      eventtime <- median(results_analysis$DayInfected[results_analysis$eventstatus==1])
      
      results_analysis$DayInfected[newevent_v_rownum] <- eventtime
      results_analysis$eventstatus[newevent_v_rownum] <- 1
      
      results_analysis$DayInfected[newevent_c_rownum] <- eventtime
      results_analysis$eventstatus[newevent_c_rownum] <- 1
      
      list[,pval_gaussian_coxme,
           ,pval_gaussian_coxph,
           ,pval_gamma_coxph,
           ,pval_gee] <- 
        clustermodels(results_analysis,VE_pointest)
      vaccEffEst_gaussian_coxme<-1
      vaccEffEst_gaussian_coxph<-1
      vaccEffEst_gamma_coxph<-1
      vaccEffEst_gee<-1
      
    } else {
      # If no events are observed in either arm, the trial has failed and no result can be obtained
      vaccEffEst_gaussian_coxme<-c(NA,NA,NA)
      pval_gaussian_coxme<-NA
      vaccEffEst_gaussian_coxph<-c(NA,NA,NA)
      pval_gaussian_coxph<-NA
      vaccEffEst_gamma_coxph<-c(NA,NA,NA)
      pval_gamma_coxph<-NA
      vaccEffEst_gee<-c(NA,NA,NA)
      pval_gee<-NA
    }
    
    list(vaccEffEst_gaussian_coxme,pval_gaussian_coxme,
         vaccEffEst_gaussian_coxph,pval_gaussian_coxph,
         vaccEffEst_gamma_coxph,pval_gamma_coxph,
         vaccEffEst_gee,pval_gee,
         numevents_vacc,numevents_cont,sample_size,ICC,deff,prop_zeros)
  }
  
}

# Initialize vectors/data frames to store results
pvals<-data.frame('iRCT'=rep(NA,nsim),
                  'cRCT_gaussian_coxme'=rep(NA,nsim),
                  'cRCT_gaussian_coxph'=rep(NA,nsim),
                  'cRCT_gamma_coxph'=rep(NA,nsim),
                  'cRCT_gee'=rep(NA,nsim))
VEs<-data.frame('iRCT'=rep(NA,nsim),
                'cRCT_gaussian_coxme'=rep(NA,nsim),
                'cRCT_gaussian_coxph'=rep(NA,nsim),
                'cRCT_gamma_coxph'=rep(NA,nsim),
                'cRCT_gee'=rep(NA,nsim))
ICCs<-rep(NA,nsim)
deffs<-rep(NA,nsim)
props_zeros <- rep(NA,nsim)
numevents_cont<-matrix(NA,nrow=2,ncol=nsim)
numevents_vacc<-matrix(NA,nrow=2,ncol=nsim)
ss<-matrix(NA,nrow=2,ncol=nsim)

for (sim in 1:nsim) {
  
  g<-make_network(ave_community_size, community_size_range, num_communities,rate_within, rate_between)
  
  list[results,trial_nodes]<-
    network_epidemic(g,beta,num_introductions,direct_VE,
                     incperiod_shape,incperiod_rate,infperiod_shape,infperiod_rate,1,0,
                     trial_startday,trial_length,num_clusters_enrolled_per_day,
                     enrollment_period,cluster_coverage,sim)
  
  list[VE,pval,events_vacc,events_cont,analysed_trialsize]<-
      analyse_data(results,trial_nodes,trial_startday,trial_length,ave_inc_period,num_clusters_perarm,0)
  pvals$iRCT[sim]<-pval
  VEs$iRCT[sim]<-VE[1]
  numevents_vacc[1,sim]<-events_vacc
  numevents_cont[1,sim]<-events_cont
  ss[1,sim]<-analysed_trialsize
  
  list[results,trial_nodes]<-
    network_epidemic(g,beta,num_introductions,direct_VE,
                     incperiod_shape,incperiod_rate,infperiod_shape,infperiod_rate,1,1,
                     trial_startday,trial_length,num_clusters_enrolled_per_day,
                     enrollment_period,cluster_coverage,sim)
  list[VE_gaussian_coxme,pval_gaussian_coxme,
         VE_gaussian_coxph,pval_gaussian_coxph,
         VE_gamma_coxph,pval_gamma_coxph,
         VE_gee,pval_gee,
         events_vacc,events_cont,analysed_trialsize,ICC,deff,prop_zeros]<-
      analyse_data(results,trial_nodes,trial_startday,trial_length,ave_inc_period,num_clusters_perarm,1)
  
  pvals$cRCT_gaussian_coxme[sim]<-pval_gaussian_coxme
  VEs$cRCT_gaussian_coxme[sim]<-VE_gaussian_coxme[1]
  
  pvals$cRCT_gaussian_coxph[sim]<-pval_gaussian_coxph
  VEs$cRCT_gaussian_coxph[sim]<-VE_gaussian_coxph[1]
  
  pvals$cRCT_gamma_coxph[sim]<-pval_gamma_coxph
  VEs$cRCT_gamma_coxph[sim]<-VE_gamma_coxph[1]
  
  pvals$cRCT_gee[sim]<-pval_gee
  VEs$cRCT_gee[sim]<-VE_gee[1]
  
  numevents_vacc[2,sim]<-events_vacc
  numevents_cont[2,sim]<-events_cont
  ss[2,sim]<-analysed_trialsize
  
  ICCs[sim]<-ICC
  deffs[sim]<-deff
  props_zeros[sim]<-prop_zeros
  
  cat("Simulation ",sim,"\n")
  
}

# Final size calculations
require(rootSolve)
require(fields)

# Compare iRCT to cRCT
# Vary VE, R0, number of introductions, and/or enrollment percentage
R0s <- c(seq(1.2,1.7,0.005))
community_size <- 100
num_communities<-100
num_intros_percluster_vec <- 1
VEs <- seq(0.3,0.6,0.005)
enrollment_percs<-c(0.6)

num_params <- length(R0s)*length(num_intros_percluster_vec)*length(VEs)*length(enrollment_percs)
# Assumption: size of minor outbreaks, when R0>1 but no major outbreak occurs
AR_nonoutbreak <- 1/community_size

index <- 1

results <- data.frame("R0"=rep(NA,num_params),
                      "num_intros"=rep(NA,num_params),
                      "VE"=rep(NA,num_params),
                      "enrollment_perc"=rep(NA,num_params),
                      "estim_VE"=rep(NA,num_params),
                      "estim_VE_iRCT"=rep(NA,num_params),
                      "cRCT_trial_CI"=rep(NA,num_params),
                      "cRCT_trial_CI_vacc"=rep(NA,num_params),
                      "cRCT_trial_CI_unvacc"=rep(NA,num_params),
                      "iRCT_trial_CI"=rep(NA,num_params),
                      "iRCT_trial_CI_vacc"=rep(NA,num_params),
                      "iRCT_trial_CI_unvacc"=rep(NA,num_params),
                      "ICC"=rep(NA,num_params),
                      "samplesize_cRCT"=rep(NA,num_params),
                      "samplesize_iRCT"=rep(NA,num_params))

for (R0 in R0s) { 
  for (num_intros_percluster in num_intros_percluster_vec) {
    for (direct_VE in VEs) {
      for (enrollment_perc in enrollment_percs) {
        
        results$R0[index]<-R0
        results$num_intros[index]<-num_intros_percluster
        results$VE[index]<-direct_VE
        results$enrollment_perc[index]<-enrollment_perc
        
        R0_vacc <- (1 - enrollment_perc * direct_VE) * R0
        
        # Final size function to solve
        # In vaccinated clusters, the CI among unvaccinated and vaccinated
        finalsizes_vacc <- function(CIs) {
          
          finalsize_U <- 1 - exp(-R0 * ((1-enrollment_perc) * CIs[1] + enrollment_perc * CIs[2])) - CIs[1]
          finalsize_V <- 1 - exp(-R0 * (1-direct_VE) * 
                                   ((1-enrollment_perc) * CIs[1] + enrollment_perc * CIs[2])) - CIs[2]
          c(F1=finalsize_U,F2=finalsize_V)
        }
        
        # In unvaccinated clusters, the CI among the unvaccinated
        finalsize_unvacc <- function(CI) {
          
          finalsize_U <- 1 - exp(-R0 * CI) - CI
          return(finalsize_U)
        }
        
        # Function to solve for outbreak probability in vaccinated clusters
        outbreakprob_vacc <- function(x) {
          prob <- exp(-R0_vacc*(1-x)) - x
          return(prob)
        }
        
        # Calculate final sizes
        if (R0_vacc>1) {
          CI_vacc<-multiroot(finalsizes_vacc,c(0.5,0.5))$root[2]
        } else {
          # This is true in large populations but is not a good approximation
          # in small populations and when R0 is close to 1
          CI_vacc <- 1/(1-R0_vacc)/community_size
        }
        if (R0>1) {
          CI_unvacc<-uniroot(finalsize_unvacc,c(1e-05,1))$root
        } else {
          # This is true in large populations but is not a good approximation
          # in small populations and when R0 is close to 1
          CI_unvacc <- 1/(1-R0)/community_size
        }
        
        # CI of vaccinated individuals in vaccinated clusters, accounting for outbreak probs
        if (R0_vacc > 1) {
          p_vacc <- 1-uniroot(outbreakprob_vacc,c(0,1-1e-05))$root
          cRCT_CI_vacc <- num_intros_percluster*(CI_vacc*p_vacc + (1-p_vacc)*AR_nonoutbreak)
          
          p_unvacc <- CI_unvacc
          cRCT_CI_unvacc <- num_intros_percluster*(CI_unvacc*p_unvacc+(1-p_unvacc)*AR_nonoutbreak)
          
          # CI_O, overall CI in the trial population
          results$cRCT_trial_CI[index] <- (cRCT_CI_unvacc+cRCT_CI_vacc)/2
          results$cRCT_trial_CI_vacc[index] <- cRCT_CI_vacc
          results$cRCT_trial_CI_unvacc[index] <- cRCT_CI_unvacc
          # Estimated VE for hazard rate analysis
          results$estim_VE[index]<-1-log(1-cRCT_CI_vacc)/log(1-cRCT_CI_unvacc)
          
          # Calculate ICC by calculating within- and between- cluster sum of squares
          # and applying the ANOVA method
          ARs <- c(rep(CI_vacc,round(num_communities*num_intros_percluster*p_vacc/2)),
                   rep(CI_unvacc,round(num_communities*num_intros_percluster*p_unvacc/2)),
                   rep(AR_nonoutbreak,round(num_communities*
                                              (1-num_intros_percluster*p_vacc/2-num_intros_percluster*p_unvacc/2))))
          cluster_size <- enrollment_perc*community_size
          numevents <- ARs*cluster_size
          
          cluster_sizes <- rep(cluster_size,num_communities)
          N <- sum(cluster_sizes)
          K <- num_communities
          n0 <- 1/(K-1) * (N - K*cluster_size^2/N)
          n01 <- 1/(K-1) * ((K-1)*n0 - K*cluster_size^2/N)
          MSB <- 1/(K-1) * sum((numevents-mean(numevents))^2/cluster_size)
          MSW <- 1/(N-K-1) * sum(numevents-numevents^2/cluster_size)
          ICC <- (MSB - MSW) / (MSB + (n01-1) * MSW)
          
          results$ICC[index]<-ICC
          DE<-1+(enrollment_perc*community_size-1)*ICC
          results$samplesize_cRCT[index] <- 
            (1.96+1.28)^2/log(1-results$estim_VE[index])^2 * DE / results$cRCT_trial_CI[index]
          
          
        } else {
          cRCT_CI_vacc <- num_intros_percluster*CI_vacc
        }
        
        # CI in iRCT
        R0_iRCT <- (1 - 0.5 * enrollment_perc * direct_VE) * R0
        finalsizes_iRCT <- function(CIs) {
          
          finalsize_U <- 1 - exp(-R0 * (enrollment_perc*0.5 * CIs[2] + (1-enrollment_perc*0.5) * CIs[1])) - CIs[1]
          finalsize_V <- 1 - exp(-R0 * (1-direct_VE) * 
                                   (enrollment_perc*0.5 * CIs[2] + (1-enrollment_perc*0.5) * CIs[1])) - CIs[2]
          c(F1=finalsize_U,F2=finalsize_V)
        }
        
        # Probability of an outbreak in a cluster (only if R0>1)
        outbreakprob_iRCT <- function(x) {
          prob <- exp(-R0_iRCT*(1-x)) - x
          return(prob)
        }
        
        if (R0_iRCT>1) {
          CIs_iRCT<-multiroot(finalsizes_iRCT,c(0.5,0.5))
          CI_vacc_iRCT<-CIs_iRCT$root[2]
          CI_unvacc_iRCT<-CIs_iRCT$root[1]
          
          p_vacc_iRCT <- 1-uniroot(outbreakprob_iRCT,c(0,1-1e-05))$root
          iRCT_CI_vacc <- num_intros_percluster*(CI_vacc_iRCT*p_vacc_iRCT + (1-p_vacc_iRCT)*AR_nonoutbreak)
          iRCT_CI_unvacc <- num_intros_percluster*(CI_unvacc_iRCT*p_vacc_iRCT + (1-p_vacc_iRCT)*AR_nonoutbreak)
          
          results$estim_VE_iRCT[index] <- 1-log(1-iRCT_CI_vacc)/log(1-iRCT_CI_unvacc)
          results$iRCT_trial_CI[index] <- (iRCT_CI_vacc+iRCT_CI_unvacc)/2
          results$iRCT_trial_CI_vacc[index] <- iRCT_CI_vacc
          results$iRCT_trial_CI_unvacc[index] <- iRCT_CI_unvacc
          results$samplesize_iRCT[index] <- (1.96+1.28)^2/log(1-results$estim_VE_iRCT[index])^2 / results$iRCT_trial_CI[index]
          
          
        } else {
          
        }
        
        index<-index+1
      }
      
    }
    
  }
  
}

results$ssratio <- results$samplesize_cRCT/results$samplesize_iRCT

# Example plot of sample size ratio, varying VE and R0
x<-matrix(results$ssratio,nrow = length(VEs),ncol=length(R0s),byrow = FALSE)
image.plot(VEs,R0s,x,
           legend.lab="cRCT/iRCT sample size ratio",
           xlab="Vaccine efficacy",
           ylab=expression(R[0]))


