#include "basis_wpms.h"
#include "wpms.h"
#include "paws.h"

char *inst;
int seed;

string version = "MAX-SAT Evaluation 2015";

int print_time=240;
int cutoff_time=296;


float rdprob;
int hd_count_threshold;

float prob;

int pick_var()
{
	int c,i,v;
	int sel_c;
	lit *p;
	int best_hscore;
	int best_sscore;
	int best_score;
	int v_score;
	
	int best_var;
	
	if( (rand()%MY_RAND_MAX_INT)*BASIC_SCALE< pacprob )
	{
		if (hardunsat_stack_fill_pointer>0) sel_c = hardunsat_stack[rand()%hardunsat_stack_fill_pointer];
		else sel_c= softunsat_stack[rand()%softunsat_stack_fill_pointer];
		return clause_lit[sel_c][rand()%clause_lit_count[sel_c]].var_num;
	}
	
	if( (rand()%MY_RAND_MAX_INT)*BASIC_SCALE< prob )
	{
		if (hardunsat_stack_fill_pointer>0) sel_c = hardunsat_stack[rand()%hardunsat_stack_fill_pointer];
		else sel_c= softunsat_stack[rand()%softunsat_stack_fill_pointer];
		
		v = clause_lit[sel_c][0].var_num;
		best_array[0] = v;
		best_count = 1;
		best_sscore = sscore[v];
		
		for(i=1; i<clause_lit_count[sel_c]; i++)
		{
			v = clause_lit[sel_c][i].var_num;
			
			if(sscore[v]>best_sscore)
			{
				best_array[0] = v;
				best_count = 1;
				best_sscore = sscore[v];
			}
			else if(sscore[v]==best_sscore)
			{
				best_array[best_count++] = v;
			}
		}
		
		return best_array[rand()%best_count];
	}
	
	if(goodvar_stack_fill_pointer>0 )
	{
        best_count=0;
        
        for(i=0; i<goodvar_stack_fill_pointer; ++i)
		{
			v = goodvar_stack[i];
            
            if(hscore[v]>0 && hard_cscc[v]==1)
            {
                best_array[best_count]=v;
                best_count++;
            }
        }
        
        if (best_count>0)
        {
            if (best_count==1) return best_array[0];

            if (best_count>hd_count_threshold && (rand()%MY_RAND_MAX_INT)*BASIC_SCALE<rdprob)
            //if( (rand()%MY_RAND_MAX_INT)*BASIC_SCALE< rdprob )
            {
            	
                int v1,v2;
                if (best_count==2) {
                    v1 = best_array[0];
                    v2 = best_array[1];
                }
                else 
                {
                    v1 = best_array[rand()%best_count];
                    v2 = best_array[rand()%best_count];
                    while (v2==v1) 
                        v2 = best_array[rand()%best_count];
                }
                
                best_var=v1;
                if(hscore[v2]>hscore[v1]) best_var=v2;
                else if(hscore[v2]==hscore[v1])
                {   
                    if (sscore[v2]>sscore[v1]) best_var=v2;
                    else if (sscore[v2]==sscore[v1] && time_stamp[v2]<time_stamp[v1]) best_var=v2;
                }

                return best_var;
            }
            
            else
            {
            	
                best_var = best_array[0];
                for (i=1; i<best_count; ++i) 
                {
                    v = best_array[i];
                    if (hscore[v]>hscore[best_var]) best_var=v;
                    else if (hscore[v]==hscore[best_var])
                    {   
                        if (sscore[v]>sscore[best_var]) best_var=v;
                        else if (sscore[v]==sscore[best_var] && time_stamp[v]<time_stamp[best_var]) best_var=v;
                    } 
                }
                return best_var;
            }
        }
	}
	
	update_hclause_weights();
	
	ccmpvars_count = 0;
	
	for(i=0; i<hardunsat_stack_fill_pointer; i++)
	{
		c = hardunsat_stack[i];
		p = clause_lit[c];
		for(; (v=p->var_num)!=0; p++)
		{
			if(conf_change[v]==1 && already_in_ccmpvars[v] != step)
			{
				ccmpvars[ccmpvars_count++] = v;
				already_in_ccmpvars[v] = step;
			}
		}
	}
	
	for(i=0; i<softunsat_stack_fill_pointer; i++)
	{
		c = softunsat_stack[i];
		p = clause_lit[c];
		for(; (v=p->var_num)!=0; p++)
		{
			if(conf_change[v]==1 && already_in_ccmpvars[v] != step)
			{
				ccmpvars[ccmpvars_count++] = v;
				already_in_ccmpvars[v] = step;
			}
		}
	}
	
	if(ccmpvars_count>0)
	{
		v = ccmpvars[0];
		best_array[0] = v;
		best_count = 1;
		best_hscore = hscore[v];
		best_sscore = sscore[v];
		
		for(i=1; i<ccmpvars_count; i++)
		{
			v = ccmpvars[i];
			
			if(hscore[v]>best_hscore)
			{
				best_array[0] = v;
				best_count = 1;
				best_hscore = hscore[v];
				best_sscore = sscore[v];
			}
			else if(hscore[v]==best_hscore)
			{
				if(sscore[v]>best_sscore)
				{
					best_array[0] = v;
					best_count = 1;
					best_sscore = sscore[v];
				}
				else if(sscore[v]==best_sscore)
				{
					best_array[best_count++] = v;
				}
			}
		}
		
		return best_array[rand()%best_count];
	}
	else
	{
		if (hardunsat_stack_fill_pointer>0) sel_c = hardunsat_stack[rand()%hardunsat_stack_fill_pointer];
		else sel_c= softunsat_stack[rand()%softunsat_stack_fill_pointer];
		return clause_lit[sel_c][rand()%clause_lit_count[sel_c]].var_num;
	}
}

void local_search(unsigned int max_flips)
{
	int flipvar;
    
	for (step = 1; step<max_flips; ++step)
	{
		if (hard_unsat_nb==0 && (soft_unsat_weight<opt_unsat_weight || best_soln_feasible==0) )
        {
            best_soln_feasible = 1;
            opt_unsat_weight = soft_unsat_weight;
			//opt_time = get_runtime();
			
			//cout<<"o "<<opt_unsat_weight<<endl;
            printf("o %lld\n", opt_unsat_weight);
            fflush(stdout);
            
            
            for(int v=1; v<=num_vars; v++) best_soln[v] = cur_soln[v];

            if(opt_unsat_weight==0) 
            {
                print_best_solution();
                return;
            }
        }
		
		flipvar = pick_var();
        
		flip(flipvar);
		time_stamp[flipvar] = step;
        
        if (step%100==0)
        {
            double elap_time = get_runtime();
            if(elap_time>=cutoff_time) return;
            if(elap_time>=print_time) break;
        }
	}
	
	//if(verify_sol()==1)
    	print_best_solution();
    
    for (; step<max_flips; step++)
	{
		if (hard_unsat_nb==0 && soft_unsat_weight<opt_unsat_weight)
        {
            best_soln_feasible = 1;
            opt_unsat_weight = soft_unsat_weight;
			//opt_time = get_runtime();
			
			//cout<<"o "<<opt_unsat_weight<<endl;
			printf("o %lld\n", opt_unsat_weight);
            fflush(stdout);
            
            for(int v=1; v<=num_vars; v++) best_soln[v] = cur_soln[v];
            
            //if(verify_sol()==1) 
            	print_best_solution();
            
            if(opt_unsat_weight==0) return;
        }
		
		if (step%100==0)
        {
            if(get_runtime()>=cutoff_time) return;            
        }
		
		flipvar = pick_var();
        
		flip(flipvar);
		time_stamp[flipvar] = step;
	}
    
}

int parse_parameters(int argc, char *argv[])
{
	int i;
	string cur_str;
	
	if(argc!=7)
	{
		return 0;
	}
	
	for(i=1; i<argc; i++)
	{
		cur_str = argv[i];
		if(cur_str.compare("-inst")==0)
		{
			i++;
			inst = argv[i];
		}
		else if(cur_str.compare("-seed")==0)
		{
			i++;
			sscanf(argv[i], "%d", &seed);
		}
		else if(cur_str.compare("-t")==0)
		{
			i++;
			sscanf(argv[i], "%d", &cutoff_time);
			print_time = cutoff_time+1;
		}
		else
		{
			return 0;
		}
	}
	return 1;
}

int main(int argc, char* argv[])
{
	int i;
	
	printf("c This is the CCEHC solver, Version: %s\n", version.c_str());
	fflush(stdout);
	
	if(argc!=7)
	{
		printf("c Usage: %s -inst <instance> -seed <seed> -t <cutoff_time>\n", argv[0]);
		fflush(stdout);
		return -1;
	}
	
	int ret = parse_parameters(argc, argv);
	if(ret==0)
	{
		printf("c Invalid parameters!\n");
		printf("c Usage: %s -inst <instance> -seed <seed> -t <cutoff_time>\n", argv[0]);
		fflush(stdout);
		return -1;
	}
	
	build_instance(inst);
	//sscanf(argv[2],"%d",&seed);
	//sscanf(argv[3],"%f",&prob);
    //sscanf(argv[2],"%d",&cutoff_time);
    
    //sscanf(argv[4],"%f",&smooth_probability);
    //sscanf(argv[5],"%d",&large_clause_count_threshold);
    
    //seed=time(0);
	//seed = 1;
	srand(seed); 
    
    set_weighting_parameters();
    
    if(num_vars==595 ) hd_count_threshold = 6; //|| num_vars==760
    else 
        hd_count_threshold=0;
    
    double ratio = ((double)num_clauses)/num_vars;
	if(ratio<1.5)
	{
		rdprob = 0;
	}
	else
	{
		rdprob = 0.6;
	}
    
    prob = 0.1;
    
    cout<<"c instance = "<<inst<<endl;
    if(probtype==UNWEIGHTED) cout<<"c problem type = unweighted"<<endl;
    else if(probtype==WEIGHTED) cout<<"c problem type = weighted"<<endl;
    else if(probtype==UNWEIGHTED_PARTIAL) cout<<"c problem type = unweighted_partial"<<endl;
    else cout<<"c problem type = weighted_partial"<<endl;
    cout<<"c seed = "<<seed<<endl;
	cout<<"c num_vars = "<<num_vars<<endl;
	cout<<"c num_clauses = "<<num_clauses<<endl;
	cout<<"c num_hclauses = "<<num_hclauses<<endl;
	cout<<"c num_sclauses = "<<num_sclauses<<endl;
	cout<<"c prob = "<<prob<<endl;
	cout<<"c sp = "<<smooth_probability<<endl;
	cout<<"c large_clause_count_threshold = "<<large_clause_count_threshold<<endl;
		 
    
	for (i=0; i<max_tries; i++) 
	{	 
		 init();
		 local_search(max_flips);

		 if(opt_unsat_weight==0) break;
		 if(get_runtime()>=cutoff_time) break;
	}
	
	//cout<<"s UNKNOWN"<<endl;
	//if(best_soln_feasible==1) 
	//	cout<<"c Best found solution with minimum cost: "<<opt_unsat_weight<<endl;
	//else cout<<"c No feasible solution found."<<endl;
    //cout<<"c search time for best_found: "<<opt_time<<endl;
    
    printf("s UNKNOWN\n");
    if(best_soln_feasible==1)
    {
    	printf("c Best found solution with minimum cost: %lld\n", opt_unsat_weight);
    	print_best_solution();
    }
    else printf("c No feasible solution found\n");
	fflush(stdout);
                        
    /*if(best_soln_feasible==1)
    {
        if(verify_sol()==1)
        {
        	//cout<<opt_unsat_weight<<' '<<opt_time<<endl;
            cout<<"s UNKNOWN"<<endl;
            print_best_solution();
            cout<<"c best_found: "<<opt_unsat_weight<<endl;
            cout<<"c search time for best_found: "<<opt_time<<endl;
             printf("c tries = %d\n", i); 
             printf("c searchSteps = %d\n", step); 
             printf("c solveTime = %lf\n",comp_time);
        }
    }
    else cout<<"c cannot find a feasible solution."<<endl;*/
	 
	free_memory();

    return 0;
}
