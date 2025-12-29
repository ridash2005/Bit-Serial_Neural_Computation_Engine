/**********************************************************************/
/*   ____  ____                                                       */
/*  /   /\/   /                                                       */
/* /___/  \  /                                                        */
/* \   \   \/                                                         */
/*  \   \        Copyright (c) 2003-2020 Xilinx, Inc.                 */
/*  /   /        All Right Reserved.                                  */
/* /---/   /\                                                         */
/* \   \  /  \                                                        */
/*  \___\/\___\                                                       */
/**********************************************************************/

#if defined(_WIN32)
 #include "stdio.h"
 #define IKI_DLLESPEC __declspec(dllimport)
#else
 #define IKI_DLLESPEC
#endif
#include "iki.h"
#include <string.h>
#include <math.h>
#ifdef __GNUC__
#include <stdlib.h>
#else
#include <malloc.h>
#define alloca _alloca
#endif
/**********************************************************************/
/*   ____  ____                                                       */
/*  /   /\/   /                                                       */
/* /___/  \  /                                                        */
/* \   \   \/                                                         */
/*  \   \        Copyright (c) 2003-2020 Xilinx, Inc.                 */
/*  /   /        All Right Reserved.                                  */
/* /---/   /\                                                         */
/* \   \  /  \                                                        */
/*  \___\/\___\                                                       */
/**********************************************************************/

#if defined(_WIN32)
 #include "stdio.h"
 #define IKI_DLLESPEC __declspec(dllimport)
#else
 #define IKI_DLLESPEC
#endif
#include "iki.h"
#include <string.h>
#include <math.h>
#ifdef __GNUC__
#include <stdlib.h>
#else
#include <malloc.h>
#define alloca _alloca
#endif
typedef void (*funcp)(char *, char *);
extern int main(int, char**);
IKI_DLLESPEC extern void execute_12(char*, char *);
IKI_DLLESPEC extern void execute_13(char*, char *);
IKI_DLLESPEC extern void execute_14(char*, char *);
IKI_DLLESPEC extern void execute_16(char*, char *);
IKI_DLLESPEC extern void execute_26(char*, char *);
IKI_DLLESPEC extern void execute_31(char*, char *);
IKI_DLLESPEC extern void execute_32(char*, char *);
IKI_DLLESPEC extern void execute_33(char*, char *);
IKI_DLLESPEC extern void execute_34(char*, char *);
IKI_DLLESPEC extern void execute_35(char*, char *);
IKI_DLLESPEC extern void execute_37(char*, char *);
IKI_DLLESPEC extern void execute_39(char*, char *);
IKI_DLLESPEC extern void svlog_sampling_process_execute(char*, char*, char*);
IKI_DLLESPEC extern void sequence_expr_m_f7c3b041_afdc3216_2(char*, char *);
IKI_DLLESPEC extern void sequence_expr_m_f7c3b041_afdc3216_3(char*, char *);
IKI_DLLESPEC extern void vlog_sv_sequence_execute_0 (char*, char*, char*);
IKI_DLLESPEC extern void assertion_action_m_f7c3b041_afdc3216_1(char*, char *);
IKI_DLLESPEC extern void sequence_expr_m_f7c3b041_afdc3216_1(char*, char *);
IKI_DLLESPEC extern void sequence_expr_m_f7c3b041_afdc3216_5(char*, char *);
IKI_DLLESPEC extern void sequence_expr_m_f7c3b041_afdc3216_6(char*, char *);
IKI_DLLESPEC extern void assertion_action_m_f7c3b041_afdc3216_2(char*, char *);
IKI_DLLESPEC extern void sequence_expr_m_f7c3b041_afdc3216_4(char*, char *);
IKI_DLLESPEC extern void sequence_expr_m_f7c3b041_afdc3216_8(char*, char *);
IKI_DLLESPEC extern void sequence_expr_m_f7c3b041_afdc3216_9(char*, char *);
IKI_DLLESPEC extern void assertion_action_m_f7c3b041_afdc3216_3(char*, char *);
IKI_DLLESPEC extern void sequence_expr_m_f7c3b041_afdc3216_7(char*, char *);
IKI_DLLESPEC extern void execute_75(char*, char *);
IKI_DLLESPEC extern void execute_76(char*, char *);
IKI_DLLESPEC extern void execute_77(char*, char *);
IKI_DLLESPEC extern void execute_78(char*, char *);
IKI_DLLESPEC extern void execute_79(char*, char *);
IKI_DLLESPEC extern void execute_80(char*, char *);
IKI_DLLESPEC extern void execute_3(char*, char *);
IKI_DLLESPEC extern void execute_4(char*, char *);
IKI_DLLESPEC extern void execute_45(char*, char *);
IKI_DLLESPEC extern void execute_46(char*, char *);
IKI_DLLESPEC extern void execute_41(char*, char *);
IKI_DLLESPEC extern void execute_42(char*, char *);
IKI_DLLESPEC extern void execute_43(char*, char *);
IKI_DLLESPEC extern void execute_44(char*, char *);
IKI_DLLESPEC extern void execute_81(char*, char *);
IKI_DLLESPEC extern void execute_82(char*, char *);
IKI_DLLESPEC extern void execute_83(char*, char *);
IKI_DLLESPEC extern void execute_84(char*, char *);
IKI_DLLESPEC extern void execute_85(char*, char *);
IKI_DLLESPEC extern void execute_86(char*, char *);
IKI_DLLESPEC extern void vlog_transfunc_eventcallback(char*, char*, unsigned, unsigned, unsigned, char *);
IKI_DLLESPEC extern void transaction_0(char*, char*, unsigned, unsigned, unsigned);
IKI_DLLESPEC extern void transaction_9(char*, char*, unsigned, unsigned, unsigned);
IKI_DLLESPEC extern void vlog_transfunc_eventcallback_2state(char*, char*, unsigned, unsigned, unsigned, char *);
funcp funcTab[50] = {(funcp)execute_12, (funcp)execute_13, (funcp)execute_14, (funcp)execute_16, (funcp)execute_26, (funcp)execute_31, (funcp)execute_32, (funcp)execute_33, (funcp)execute_34, (funcp)execute_35, (funcp)execute_37, (funcp)execute_39, (funcp)svlog_sampling_process_execute, (funcp)sequence_expr_m_f7c3b041_afdc3216_2, (funcp)sequence_expr_m_f7c3b041_afdc3216_3, (funcp)vlog_sv_sequence_execute_0 , (funcp)assertion_action_m_f7c3b041_afdc3216_1, (funcp)sequence_expr_m_f7c3b041_afdc3216_1, (funcp)sequence_expr_m_f7c3b041_afdc3216_5, (funcp)sequence_expr_m_f7c3b041_afdc3216_6, (funcp)assertion_action_m_f7c3b041_afdc3216_2, (funcp)sequence_expr_m_f7c3b041_afdc3216_4, (funcp)sequence_expr_m_f7c3b041_afdc3216_8, (funcp)sequence_expr_m_f7c3b041_afdc3216_9, (funcp)assertion_action_m_f7c3b041_afdc3216_3, (funcp)sequence_expr_m_f7c3b041_afdc3216_7, (funcp)execute_75, (funcp)execute_76, (funcp)execute_77, (funcp)execute_78, (funcp)execute_79, (funcp)execute_80, (funcp)execute_3, (funcp)execute_4, (funcp)execute_45, (funcp)execute_46, (funcp)execute_41, (funcp)execute_42, (funcp)execute_43, (funcp)execute_44, (funcp)execute_81, (funcp)execute_82, (funcp)execute_83, (funcp)execute_84, (funcp)execute_85, (funcp)execute_86, (funcp)vlog_transfunc_eventcallback, (funcp)transaction_0, (funcp)transaction_9, (funcp)vlog_transfunc_eventcallback_2state};
const int NumRelocateId= 50;

void relocate(char *dp)
{
	iki_relocate(dp, "xsim.dir/tb_mac_engine_behav/xsim.reloc",  (void **)funcTab, 50);

	/*Populate the transaction function pointer field in the whole net structure */
}

void sensitize(char *dp)
{
	iki_sensitize(dp, "xsim.dir/tb_mac_engine_behav/xsim.reloc");
}

void simulate(char *dp)
{
		iki_schedule_processes_at_time_zero(dp, "xsim.dir/tb_mac_engine_behav/xsim.reloc");
	// Initialize Verilog nets in mixed simulation, for the cases when the value at time 0 should be propagated from the mixed language Vhdl net
	iki_execute_processes();

	// Schedule resolution functions for the multiply driven Verilog nets that have strength
	// Schedule transaction functions for the singly driven Verilog nets that have strength

}
#include "iki_bridge.h"
void relocate(char *);

void sensitize(char *);

void simulate(char *);

extern SYSTEMCLIB_IMP_DLLSPEC void local_register_implicit_channel(int, char*);
extern SYSTEMCLIB_IMP_DLLSPEC int xsim_argc_copy ;
extern SYSTEMCLIB_IMP_DLLSPEC char** xsim_argv_copy ;

int main(int argc, char **argv)
{
    iki_heap_initialize("ms", "isimmm", 0, 2147483648) ;
    iki_set_xsimdir_location_if_remapped(argc, argv)  ;
    iki_set_sv_type_file_path_name("xsim.dir/tb_mac_engine_behav/xsim.svtype");
    iki_set_crvs_dump_file_path_name("xsim.dir/tb_mac_engine_behav/xsim.crvsdump");
    void* design_handle = iki_create_design("xsim.dir/tb_mac_engine_behav/xsim.mem", (void *)relocate, (void *)sensitize, (void *)simulate, (void*)0, 0, isimBridge_getWdbWriter(), 0, argc, argv);
     iki_set_rc_trial_count(100);
    (void) design_handle;
    return iki_simulate_design();
}
