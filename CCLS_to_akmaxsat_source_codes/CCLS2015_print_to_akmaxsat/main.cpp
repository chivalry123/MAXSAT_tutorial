#include "basic.h"

#include <time.h>
#include <sys/times.h> //these two h files are for linux
#include <unistd.h>

string version = "MAX-SAT Evaluation 2015";

unsigned long long step;
//struct tms start, stop;
//int print_time=240;
//int cutoff_time=296;

const int MY_RAND_MAX_INT = 10000000;
const int prob1 = 370*10000; //random weighted max2sat
const int prob2 = 420*10000; //random weighted max3sat
const int prob3 = 200*10000; //not random weighted

const int prob4 = 300*10000; //random unweighted max3sat
const int prob5 = 400*10000; //random unweighted max4sat
const int prob6 = 100*10000; //unweighted

int prob = 200*10000; //default

void (* local_search)();

int pick_var()
{
	int     i,c,v;
	int     best_score=0;
	int		v_score;
	
	if(rand()%MY_RAND_MAX_INT<prob)
	{
		c = unsat_stack[rand()%unsat_stack_fill_pointer];
		return clause_lit[c][rand()%clause_lit_count[c]].var_num;
	}
	
	best_array_count=0;
	for(i=0; i<unsatvar_stack_fill_pointer; i++)
	{
		v = unsatvar_stack[i];
		if(conf_change[v]==1)
		{
			best_array[0] = v;
			best_array_count=1;
			best_score = score[v];
			break;
		}
	}
	for(i++; i<unsatvar_stack_fill_pointer; i++)
	{
		v = unsatvar_stack[i];
		if(conf_change[v]==0)
			continue;
		v_score = score[v];
		if(v_score>best_score)
		{
			best_array[0] = v;
			best_array_count=1;
			best_score = v_score;
		}
		else if(v_score==best_score)
			best_array[best_array_count++] = v;
	}
	
	if(best_array_count>0)
		return best_array[rand()%best_array_count];
	
	c = unsat_stack[rand()%unsat_stack_fill_pointer];
	return clause_lit[c][rand()%clause_lit_count[c]].var_num;
}


void local_search_non_partial()
{
	int flipvar,v,j;
	if(opt_unsat_clause_weight>total_unsat_clause_weight)
	{
		opt_unsat_clause_weight=total_unsat_clause_weight;
		//printf("o %llu\n",opt_unsat_clause_weight);
		//fflush(stdout);
		//times(&stop);
		//opt_time = (double)(stop.tms_utime - start.tms_utime +stop.tms_stime - start.tms_stime) / sysconf(_SC_CLK_TCK);
		for(v=1; v<=num_vars; v++)
			best_soln[v] = cur_soln[v];
		opt_unsat_clause_count = unsat_stack_fill_pointer;
	}
	if(total_unsat_clause_weight==0)
	{
		//print_solution();
		return;
	}
	
	for(step=0; step<max_flips;)
	{
		for(j=0; j<100; j++, step++)
		{
			if(opt_unsat_clause_weight>total_unsat_clause_weight)
			{
				opt_unsat_clause_weight=total_unsat_clause_weight;
				//printf("o %llu\n",opt_unsat_clause_weight);
				//fflush(stdout);
				//times(&stop);
				//opt_time = (double)(stop.tms_utime - start.tms_utime +stop.tms_stime - start.tms_stime) / sysconf(_SC_CLK_TCK);
				for(v=1; v<=num_vars; v++)
					best_soln[v] = cur_soln[v];
				opt_unsat_clause_count = unsat_stack_fill_pointer;
			}
			if(total_unsat_clause_weight==0) 
			{
				//print_solution();
				return;
			}
			flipvar = pick_var();
			flip(flipvar);
		}
		//times(&stop);
		//double elap_time = (stop.tms_utime - start.tms_utime +stop.tms_stime - start.tms_stime) / sysconf(_SC_CLK_TCK);
		//if(elap_time >= cutoff_time)return;
		//if(elap_time >= print_time) break;
	}
	/*
	print_solution();
	for(; step<max_flips;)
	{
		for(j=0; j<100; j++, step++)
		{
			if(opt_unsat_clause_weight>total_unsat_clause_weight)
			{
				opt_unsat_clause_weight=total_unsat_clause_weight;
				printf("o %llu\n",opt_unsat_clause_weight);
				fflush(stdout);
				times(&stop);
				opt_time = (double)(stop.tms_utime - start.tms_utime +stop.tms_stime - start.tms_stime) / sysconf(_SC_CLK_TCK);
				for(v=1; v<=num_vars; v++)
					best_soln[v] = cur_soln[v];
				print_solution();
				opt_unsat_clause_count = unsat_stack_fill_pointer;
			}
			if(total_unsat_clause_weight==0) return;
			flipvar = pick_var();
			flip(flipvar);
		}
		//times(&stop);
		//double elap_time = (stop.tms_utime - start.tms_utime +stop.tms_stime - start.tms_stime) / sysconf(_SC_CLK_TCK);
		//if(elap_time >= cutoff_time)return;
	}
	*/
}

void local_search_partial()
{
	int flipvar,v,j;
	if(total_unsat_clause_weight<hard_clause_weight && opt_unsat_clause_weight>total_unsat_clause_weight)
	{
		opt_unsat_clause_weight=total_unsat_clause_weight;
		//printf("o %llu\n",opt_unsat_clause_weight);
		//fflush(stdout);
		//times(&stop);
		//opt_time = (double)(stop.tms_utime - start.tms_utime +stop.tms_stime - start.tms_stime) / sysconf(_SC_CLK_TCK);
		for(v=1; v<=num_vars; v++)
			best_soln[v] = cur_soln[v];
		opt_unsat_clause_count = unsat_stack_fill_pointer;
	}
	if(total_unsat_clause_weight==0)
	{
		//print_solution();
		return;
	}
	
	for(step=0; step<max_flips;)
	{
		for(j=0; j<100; j++, step++)
		{
			if(total_unsat_clause_weight<hard_clause_weight && opt_unsat_clause_weight>total_unsat_clause_weight)
			{
				opt_unsat_clause_weight=total_unsat_clause_weight;
				//printf("o %llu\n",opt_unsat_clause_weight);
				//fflush(stdout);
				//times(&stop);
				//opt_time = (double)(stop.tms_utime - start.tms_utime +stop.tms_stime - start.tms_stime) / sysconf(_SC_CLK_TCK);
				for(v=1; v<=num_vars; v++)
					best_soln[v] = cur_soln[v];
				opt_unsat_clause_count = unsat_stack_fill_pointer;
			}
			if(total_unsat_clause_weight==0) 
			{
				//print_solution();
				return;
			}
			flipvar = pick_var();
			flip(flipvar);
		}
		//times(&stop);
		//double elap_time = (stop.tms_utime - start.tms_utime +stop.tms_stime - start.tms_stime) / sysconf(_SC_CLK_TCK);
		//if(elap_time >= cutoff_time)return;
		//if(elap_time >= print_time) break;
	}
	/*
	if(opt_unsat_clause_weight<hard_clause_weight)
		print_solution();
	for(; step<max_flips;)
	{
		for(j=0; j<100; j++, step++)
		{
			if(total_unsat_clause_weight<hard_clause_weight && opt_unsat_clause_weight>total_unsat_clause_weight)
			{
				opt_unsat_clause_weight=total_unsat_clause_weight;
				printf("o %llu\n",opt_unsat_clause_weight);
				fflush(stdout);
				times(&stop);
				opt_time = (double)(stop.tms_utime - start.tms_utime +stop.tms_stime - start.tms_stime) / sysconf(_SC_CLK_TCK);
				for(v=1; v<=num_vars; v++)
					best_soln[v] = cur_soln[v];
					print_solution();
				opt_unsat_clause_count = unsat_stack_fill_pointer;
			}
			if(total_unsat_clause_weight==0) return;
			flipvar = pick_var();
			flip(flipvar);
		}
		//times(&stop);
		//double elap_time = (stop.tms_utime - start.tms_utime +stop.tms_stime - start.tms_stime) / sysconf(_SC_CLK_TCK);
		//if(elap_time >= cutoff_time)return;
	}
	*/
}



void select_prob_and_method()
{
	if(probtype==WEIGHTED) //weighted
	{
		local_search = local_search_non_partial;
		
		if(maxi_clause_len==mini_clause_len && maxi_clause_weight-mini_clause_weight<diff_crafted_weight)
		{
			if(maxi_clause_len<=2)
			{
				prob = prob1;
			}
			else
			{
				prob = prob2;
			}
		}
		else
		{
			prob = prob3;
		}
	}
	else if(probtype==UNWEIGHTED) //unweighted
	{
		local_search = local_search_non_partial;
	
		if(maxi_clause_len==mini_clause_len)
		{
			if(maxi_clause_len==3)
			{
				prob = prob4;
			}
			else if(maxi_clause_len>=4)
			{
				prob = prob5;
			}
		}
		else
		{
			prob = prob6;
		}
	}
	else //weighted_partial
	{
		//local_search = local_search_partial;
		local_search = local_search_non_partial;
	
		if(maxi_clause_len==mini_clause_len)
		{
			if(maxi_clause_len<=2)
			{
				prob = prob1;
			}
			else
			{
				prob = prob2;
			}
		}
		else
		{
			prob = prob3;
		}
	}
}

void print_information(char* instance, int seed)
{
	printf("c instance = %s\n", instance);
	if(probtype==WEIGHTED)
		printf("c problem type = weighted\n");
	else if(probtype==UNWEIGHTED)
		printf("c problem type = unweighted\n");
	else printf("c problem type = weighted_partial\n");
	printf("c seed = %d\n", seed);
	printf("c num_vars = %d\nc num_clauses = %d\n", num_vars, num_clauses);
    printf("c maxi_clause_len = %d\nc mini_clause_len = %d\nc maxi_clause_weight = %lld\nc mini_clause_weight = %lld\nc prob = %lf\n", maxi_clause_len, mini_clause_len, maxi_clause_weight, mini_clause_weight, (double)prob/MY_RAND_MAX_INT);
    fflush(stdout);
}

int main(int argc, char* argv[])
{
	int     seed;
	unsigned long long tries;
	
	//printf("c This is the CCLS solver, Version: %s\n", version.c_str());
	//fflush(stdout);
	
	//times(&start);
	probtype = NONE;
	
	if (argc!=4)
	{
		printf("c Usage: %s <instance> <seed> <max_tries>\n", argv[0]);
		fflush(stdout);
		return -1;
	}
	
	if (build_instance(argv[1])==0)
	{
		printf("c Invalid filename: %s\n", argv[1]);
		fflush(stdout);
		return -1;
	}
	
    sscanf(argv[2],"%d",&seed);
    //seed = time(0);
	srand(seed);
	
	//sscanf(argv[3], "%d", &cutoff_time);
	//print_time = cutoff_time+10;
	
	sscanf(argv[3],"%llu",&max_tries);
	if(500*num_vars<500000) max_flips = 500*num_vars;
	else max_flips = 500000;
	
	select_prob_and_method();
	//print_information(argv[1], seed);
	
	opt_unsat_clause_weight = total_clause_weight+1;

	printf("# CCLS\n");

	for (tries = 1; tries <= max_tries; tries++) 
	{
		 init();
		 local_search();
		 //if (unsat_stack_fill_pointer==0)  break;
		 
		 printf("%llu 0 %llu ", tries, opt_unsat_clause_weight);
		 int v;
		 for(v=1; v<=num_vars; v++)
		 {
		 	if(best_soln[v]==0) printf("0");
		 	else printf("1");
		 }
		 printf("\n");
		 
		 //times(&stop);
		 //double elap_time = (stop.tms_utime - start.tms_utime +stop.tms_stime - start.tms_stime) / sysconf(_SC_CLK_TCK);
		 //if(elap_time >= cutoff_time) break;
	}

	/*
	times(&stop);
	double comp_time = double(stop.tms_utime - start.tms_utime +stop.tms_stime - start.tms_stime) / sysconf(_SC_CLK_TCK);

     //print out information about the solution.
	if(probtype==WEIGHTED || probtype==UNWEIGHTED)
	{
		if(verify_sol_non_partial()==1)
		{
			//printf("%d sat %llu %llu %lf\n",seed,tries,step,comp_time);
			 //printf("s SATISFIABLE\n");
			 //print_solution();
			 printf("s UNKNOWN\n");
			 printf("c instance = %s\n", argv[1]);
		 	 printf("c seed = %d\n", seed);
			 printf("c verifying successful!\n");
			 printf("c tries = %llu\n", tries); 
			 printf("c searchSteps = %llu\n", step);
			 printf("c optSatWeightsTotal(Total-optUnsatWeightsTotal) = %llu\n", total_clause_weight-opt_unsat_clause_weight);
			 printf("c optUnsatWeightsTotal = %llu\n", opt_unsat_clause_weight);
			 printf("c optUnsatClausesCount = %lld\n", opt_unsat_clause_count);  
			 printf("c optTime = %lf\n",opt_time);
			 printf("c totalTime = %lf\n",comp_time);
			 fflush(stdout);
		 }
		 else
		 {
		     printf("s UNKNOWN\n");
		 	 printf("c instance = %s\n", argv[1]);
		 	 printf("c seed = %d\n", seed);
		 	 printf("c failure\n");
		 	 fflush(stdout);
		 }
	}
	else
	{
		if(verify_sol_partial()==1)
		{
			//printf("%d sat %llu %llu %lf\n",seed,tries,step,comp_time);
			 //printf("s SATISFIABLE\n");
			 //print_solution();
			 printf("s UNKNOWN\n");
			 printf("c instance = %s\n", argv[1]);
		 	 printf("c seed = %d\n", seed);
			 printf("c verifying successful!\n");
			 printf("c tries = %llu\n", tries); 
			 printf("c searchSteps = %llu\n", step);
			 printf("c optSatWeightsTotal(Total-optUnsatWeightsTotal) = %llu\n", total_clause_weight-opt_unsat_clause_weight);
			 printf("c optUnsatWeightsTotal = %llu\n", opt_unsat_clause_weight);
			 printf("c optUnsatClausesCount = %lld\n", opt_unsat_clause_count);  
			 printf("c optTime = %lf\n",opt_time);
			 printf("c totalTime = %lf\n",comp_time);
			 fflush(stdout);
		 }
		 else
		 {
		 	printf("s UNKNOWN\n");
		 	printf("c instance = %s\n", argv[1]);
		 	printf("c seed = %d\n", seed);
		 	printf("c failure\n");
		 	if(opt_unsat_clause_weight>=hard_clause_weight)
		 		printf("c this instance seems to be UNSAT\n");	
		 	fflush(stdout);
		 }
	}
	*/
	free_memory();

    return 0;
}

