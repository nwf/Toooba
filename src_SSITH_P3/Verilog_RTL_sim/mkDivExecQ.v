//
// Generated by Bluespec Compiler, version 2019.05.beta2 (build a88bf40db, 2019-05-24)
//
// On Thu Jul  2 02:55:57 BST 2020
//
//
// Ports:
// Name                         I/O  size props
// RDY_enq                        O     1
// RDY_deq                        O     1
// first_data                     O    36
// RDY_first_data                 O     1
// first_poisoned                 O     1
// RDY_first_poisoned             O     1
// RDY_specUpdate_incorrectSpeculation  O     1 const
// RDY_specUpdate_correctSpeculation  O     1 const
// CLK                            I     1 clock
// RST_N                          I     1 reset
// enq_x                          I    36
// specUpdate_incorrectSpeculation_kill_all  I     1
// specUpdate_incorrectSpeculation_kill_tag  I     4
// specUpdate_correctSpeculation_mask  I    12
// EN_enq                         I     1
// EN_deq                         I     1
// EN_specUpdate_incorrectSpeculation  I     1
// EN_specUpdate_correctSpeculation  I     1
//
// No combinational paths from inputs to outputs
//
//

`ifdef BSV_ASSIGNMENT_DELAY
`else
  `define BSV_ASSIGNMENT_DELAY
`endif

`ifdef BSV_POSITIVE_RESET
  `define BSV_RESET_VALUE 1'b1
  `define BSV_RESET_EDGE posedge
`else
  `define BSV_RESET_VALUE 1'b0
  `define BSV_RESET_EDGE negedge
`endif

module mkDivExecQ(CLK,
		  RST_N,

		  enq_x,
		  EN_enq,
		  RDY_enq,

		  EN_deq,
		  RDY_deq,

		  first_data,
		  RDY_first_data,

		  first_poisoned,
		  RDY_first_poisoned,

		  specUpdate_incorrectSpeculation_kill_all,
		  specUpdate_incorrectSpeculation_kill_tag,
		  EN_specUpdate_incorrectSpeculation,
		  RDY_specUpdate_incorrectSpeculation,

		  specUpdate_correctSpeculation_mask,
		  EN_specUpdate_correctSpeculation,
		  RDY_specUpdate_correctSpeculation);
  input  CLK;
  input  RST_N;

  // action method enq
  input  [35 : 0] enq_x;
  input  EN_enq;
  output RDY_enq;

  // action method deq
  input  EN_deq;
  output RDY_deq;

  // value method first_data
  output [35 : 0] first_data;
  output RDY_first_data;

  // value method first_poisoned
  output first_poisoned;
  output RDY_first_poisoned;

  // action method specUpdate_incorrectSpeculation
  input  specUpdate_incorrectSpeculation_kill_all;
  input  [3 : 0] specUpdate_incorrectSpeculation_kill_tag;
  input  EN_specUpdate_incorrectSpeculation;
  output RDY_specUpdate_incorrectSpeculation;

  // action method specUpdate_correctSpeculation
  input  [11 : 0] specUpdate_correctSpeculation_mask;
  input  EN_specUpdate_correctSpeculation;
  output RDY_specUpdate_correctSpeculation;

  // signals for module outputs
  reg RDY_deq, first_poisoned;
  wire [35 : 0] first_data;
  wire RDY_enq,
       RDY_first_data,
       RDY_first_poisoned,
       RDY_specUpdate_correctSpeculation,
       RDY_specUpdate_incorrectSpeculation;

  // inlined wires
  reg m_valid_for_enq_wire$wget;
  wire [11 : 0] m_specBits_0_lat_1$wget, m_specBits_1_lat_1$wget;
  wire m_poisoned_0_lat_0$whas,
       m_poisoned_1_lat_0$whas,
       m_valid_0_lat_0$whas,
       m_valid_0_lat_1$whas,
       m_valid_1_lat_0$whas,
       m_valid_1_lat_1$whas;

  // register m_deqP
  reg m_deqP;
  wire m_deqP$D_IN, m_deqP$EN;

  // register m_enqP
  reg m_enqP;
  wire m_enqP$D_IN, m_enqP$EN;

  // register m_poisoned_0_rl
  reg m_poisoned_0_rl;
  wire m_poisoned_0_rl$D_IN, m_poisoned_0_rl$EN;

  // register m_poisoned_1_rl
  reg m_poisoned_1_rl;
  wire m_poisoned_1_rl$D_IN, m_poisoned_1_rl$EN;

  // register m_row_0
  reg [23 : 0] m_row_0;
  wire [23 : 0] m_row_0$D_IN;
  wire m_row_0$EN;

  // register m_row_1
  reg [23 : 0] m_row_1;
  wire [23 : 0] m_row_1$D_IN;
  wire m_row_1$EN;

  // register m_specBits_0_rl
  reg [11 : 0] m_specBits_0_rl;
  wire [11 : 0] m_specBits_0_rl$D_IN;
  wire m_specBits_0_rl$EN;

  // register m_specBits_1_rl
  reg [11 : 0] m_specBits_1_rl;
  wire [11 : 0] m_specBits_1_rl$D_IN;
  wire m_specBits_1_rl$EN;

  // register m_valid_0_rl
  reg m_valid_0_rl;
  wire m_valid_0_rl$D_IN, m_valid_0_rl$EN;

  // register m_valid_1_rl
  reg m_valid_1_rl;
  wire m_valid_1_rl$D_IN, m_valid_1_rl$EN;

  // rule scheduling signals
  wire CAN_FIRE_RL_m_poisoned_0_canon,
       CAN_FIRE_RL_m_poisoned_1_canon,
       CAN_FIRE_RL_m_setEnqWire,
       CAN_FIRE_RL_m_specBits_0_canon,
       CAN_FIRE_RL_m_specBits_1_canon,
       CAN_FIRE_RL_m_valid_0_canon,
       CAN_FIRE_RL_m_valid_1_canon,
       CAN_FIRE_deq,
       CAN_FIRE_enq,
       CAN_FIRE_specUpdate_correctSpeculation,
       CAN_FIRE_specUpdate_incorrectSpeculation,
       WILL_FIRE_RL_m_poisoned_0_canon,
       WILL_FIRE_RL_m_poisoned_1_canon,
       WILL_FIRE_RL_m_setEnqWire,
       WILL_FIRE_RL_m_specBits_0_canon,
       WILL_FIRE_RL_m_specBits_1_canon,
       WILL_FIRE_RL_m_valid_0_canon,
       WILL_FIRE_RL_m_valid_1_canon,
       WILL_FIRE_deq,
       WILL_FIRE_enq,
       WILL_FIRE_specUpdate_correctSpeculation,
       WILL_FIRE_specUpdate_incorrectSpeculation;

  // remaining internal signals
  reg [11 : 0] CASE_m_deqP_0_m_specBits_0_rl_1_m_specBits_1_r_ETC__q9;
  reg [6 : 0] CASE_m_deqP_0_m_row_0_BITS_19_TO_13_1_m_row_1__ETC__q5;
  reg [5 : 0] CASE_m_deqP_0_m_row_0_BITS_5_TO_0_1_m_row_1_BI_ETC__q3;
  reg [4 : 0] CASE_m_deqP_0_m_row_0_BITS_10_TO_6_1_m_row_1_B_ETC__q2;
  reg [1 : 0] CASE_m_deqP_0_m_row_0_BITS_23_TO_22_1_m_row_1__ETC__q8;
  reg CASE_m_deqP_0_NOT_m_row_0_BIT_20_1_NOT_m_row_1_ETC__q4,
      CASE_m_deqP_0_m_row_0_BIT_11_1_m_row_1_BIT_11__ETC__q1,
      CASE_m_deqP_0_m_row_0_BIT_12_1_m_row_1_BIT_12__ETC__q6,
      CASE_m_deqP_0_m_row_0_BIT_21_1_m_row_1_BIT_21__ETC__q7;
  wire [21 : 0] SEL_ARR_m_row_0_7_BIT_21_3_m_row_1_9_BIT_21_4__ETC___d108;
  wire [11 : 0] SEL_ARR_m_row_0_7_BIT_11_5_m_row_1_9_BIT_11_6__ETC___d107,
		n__read__h5092,
		n__read__h5222,
		upd__h2523,
		upd__h2868;
  wire [8 : 0] NOT_SEL_ARR_NOT_m_row_0_7_BIT_20_7_8_NOT_m_row_ETC___d94;

  // action method enq
  assign RDY_enq = !m_valid_for_enq_wire$wget ;
  assign CAN_FIRE_enq = !m_valid_for_enq_wire$wget ;
  assign WILL_FIRE_enq = EN_enq ;

  // action method deq
  always@(m_deqP or m_valid_0_rl or m_valid_1_rl)
  begin
    case (m_deqP)
      1'd0: RDY_deq = m_valid_0_rl;
      1'd1: RDY_deq = m_valid_1_rl;
    endcase
  end
  assign CAN_FIRE_deq = RDY_deq ;
  assign WILL_FIRE_deq = EN_deq ;

  // value method first_data
  assign first_data =
	     { CASE_m_deqP_0_m_row_0_BITS_23_TO_22_1_m_row_1__ETC__q8,
	       SEL_ARR_m_row_0_7_BIT_21_3_m_row_1_9_BIT_21_4__ETC___d108,
	       CASE_m_deqP_0_m_specBits_0_rl_1_m_specBits_1_r_ETC__q9 } ;
  assign RDY_first_data = RDY_deq ;

  // value method first_poisoned
  always@(m_deqP or m_poisoned_0_rl or m_poisoned_1_rl)
  begin
    case (m_deqP)
      1'd0: first_poisoned = m_poisoned_0_rl;
      1'd1: first_poisoned = m_poisoned_1_rl;
    endcase
  end
  assign RDY_first_poisoned = RDY_deq ;

  // action method specUpdate_incorrectSpeculation
  assign RDY_specUpdate_incorrectSpeculation = 1'd1 ;
  assign CAN_FIRE_specUpdate_incorrectSpeculation = 1'd1 ;
  assign WILL_FIRE_specUpdate_incorrectSpeculation =
	     EN_specUpdate_incorrectSpeculation ;

  // action method specUpdate_correctSpeculation
  assign RDY_specUpdate_correctSpeculation = 1'd1 ;
  assign CAN_FIRE_specUpdate_correctSpeculation = 1'd1 ;
  assign WILL_FIRE_specUpdate_correctSpeculation =
	     EN_specUpdate_correctSpeculation ;

  // rule RL_m_setEnqWire
  assign CAN_FIRE_RL_m_setEnqWire = 1'd1 ;
  assign WILL_FIRE_RL_m_setEnqWire = 1'd1 ;

  // rule RL_m_valid_0_canon
  assign CAN_FIRE_RL_m_valid_0_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_valid_0_canon = 1'd1 ;

  // rule RL_m_valid_1_canon
  assign CAN_FIRE_RL_m_valid_1_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_valid_1_canon = 1'd1 ;

  // rule RL_m_poisoned_0_canon
  assign CAN_FIRE_RL_m_poisoned_0_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_poisoned_0_canon = 1'd1 ;

  // rule RL_m_poisoned_1_canon
  assign CAN_FIRE_RL_m_poisoned_1_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_poisoned_1_canon = 1'd1 ;

  // rule RL_m_specBits_0_canon
  assign CAN_FIRE_RL_m_specBits_0_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_specBits_0_canon = 1'd1 ;

  // rule RL_m_specBits_1_canon
  assign CAN_FIRE_RL_m_specBits_1_canon = 1'd1 ;
  assign WILL_FIRE_RL_m_specBits_1_canon = 1'd1 ;

  // inlined wires
  assign m_valid_0_lat_0$whas = EN_deq && m_deqP == 1'd0 ;
  assign m_valid_0_lat_1$whas = EN_enq && m_enqP == 1'd0 ;
  assign m_valid_1_lat_0$whas = EN_deq && m_deqP == 1'd1 ;
  assign m_valid_1_lat_1$whas = EN_enq && m_enqP == 1'd1 ;
  assign m_poisoned_0_lat_0$whas =
	     EN_specUpdate_incorrectSpeculation &&
	     (specUpdate_incorrectSpeculation_kill_all ||
	      m_specBits_0_rl[specUpdate_incorrectSpeculation_kill_tag]) ;
  assign m_poisoned_1_lat_0$whas =
	     EN_specUpdate_incorrectSpeculation &&
	     (specUpdate_incorrectSpeculation_kill_all ||
	      m_specBits_1_rl[specUpdate_incorrectSpeculation_kill_tag]) ;
  assign m_specBits_0_lat_1$wget =
	     n__read__h5092 & specUpdate_correctSpeculation_mask ;
  assign m_specBits_1_lat_1$wget =
	     n__read__h5222 & specUpdate_correctSpeculation_mask ;
  always@(m_enqP or m_valid_0_rl or m_valid_1_rl)
  begin
    case (m_enqP)
      1'd0: m_valid_for_enq_wire$wget = m_valid_0_rl;
      1'd1: m_valid_for_enq_wire$wget = m_valid_1_rl;
    endcase
  end

  // register m_deqP
  assign m_deqP$D_IN = m_deqP + 1'd1 ;
  assign m_deqP$EN = EN_deq ;

  // register m_enqP
  assign m_enqP$D_IN = m_enqP + 1'd1 ;
  assign m_enqP$EN = EN_enq ;

  // register m_poisoned_0_rl
  assign m_poisoned_0_rl$D_IN =
	     !m_valid_0_lat_1$whas &&
	     (m_poisoned_0_lat_0$whas || m_poisoned_0_rl) ;
  assign m_poisoned_0_rl$EN = 1'd1 ;

  // register m_poisoned_1_rl
  assign m_poisoned_1_rl$D_IN =
	     !m_valid_1_lat_1$whas &&
	     (m_poisoned_1_lat_0$whas || m_poisoned_1_rl) ;
  assign m_poisoned_1_rl$EN = 1'd1 ;

  // register m_row_0
  assign m_row_0$D_IN = enq_x[35:12] ;
  assign m_row_0$EN = m_valid_0_lat_1$whas ;

  // register m_row_1
  assign m_row_1$D_IN = enq_x[35:12] ;
  assign m_row_1$EN = m_valid_1_lat_1$whas ;

  // register m_specBits_0_rl
  assign m_specBits_0_rl$D_IN =
	     EN_specUpdate_correctSpeculation ? upd__h2523 : n__read__h5092 ;
  assign m_specBits_0_rl$EN = 1'd1 ;

  // register m_specBits_1_rl
  assign m_specBits_1_rl$D_IN =
	     EN_specUpdate_correctSpeculation ? upd__h2868 : n__read__h5222 ;
  assign m_specBits_1_rl$EN = 1'd1 ;

  // register m_valid_0_rl
  assign m_valid_0_rl$D_IN =
	     m_valid_0_lat_1$whas || !m_valid_0_lat_0$whas && m_valid_0_rl ;
  assign m_valid_0_rl$EN = 1'd1 ;

  // register m_valid_1_rl
  assign m_valid_1_rl$D_IN =
	     m_valid_1_lat_1$whas || !m_valid_1_lat_0$whas && m_valid_1_rl ;
  assign m_valid_1_rl$EN = 1'd1 ;

  // remaining internal signals
  assign NOT_SEL_ARR_NOT_m_row_0_7_BIT_20_7_8_NOT_m_row_ETC___d94 =
	     { !CASE_m_deqP_0_NOT_m_row_0_BIT_20_1_NOT_m_row_1_ETC__q4,
	       CASE_m_deqP_0_m_row_0_BITS_19_TO_13_1_m_row_1__ETC__q5,
	       CASE_m_deqP_0_m_row_0_BIT_12_1_m_row_1_BIT_12__ETC__q6 } ;
  assign SEL_ARR_m_row_0_7_BIT_11_5_m_row_1_9_BIT_11_6__ETC___d107 =
	     { CASE_m_deqP_0_m_row_0_BIT_11_1_m_row_1_BIT_11__ETC__q1,
	       CASE_m_deqP_0_m_row_0_BITS_10_TO_6_1_m_row_1_B_ETC__q2,
	       CASE_m_deqP_0_m_row_0_BITS_5_TO_0_1_m_row_1_BI_ETC__q3 } ;
  assign SEL_ARR_m_row_0_7_BIT_21_3_m_row_1_9_BIT_21_4__ETC___d108 =
	     { CASE_m_deqP_0_m_row_0_BIT_21_1_m_row_1_BIT_21__ETC__q7,
	       NOT_SEL_ARR_NOT_m_row_0_7_BIT_20_7_8_NOT_m_row_ETC___d94,
	       SEL_ARR_m_row_0_7_BIT_11_5_m_row_1_9_BIT_11_6__ETC___d107 } ;
  assign n__read__h5092 =
	     m_valid_0_lat_1$whas ? enq_x[11:0] : m_specBits_0_rl ;
  assign n__read__h5222 =
	     m_valid_1_lat_1$whas ? enq_x[11:0] : m_specBits_1_rl ;
  assign upd__h2523 = m_specBits_0_lat_1$wget ;
  assign upd__h2868 = m_specBits_1_lat_1$wget ;
  always@(m_deqP or m_row_0 or m_row_1)
  begin
    case (m_deqP)
      1'd0:
	  CASE_m_deqP_0_m_row_0_BIT_11_1_m_row_1_BIT_11__ETC__q1 =
	      m_row_0[11];
      1'd1:
	  CASE_m_deqP_0_m_row_0_BIT_11_1_m_row_1_BIT_11__ETC__q1 =
	      m_row_1[11];
    endcase
  end
  always@(m_deqP or m_row_0 or m_row_1)
  begin
    case (m_deqP)
      1'd0:
	  CASE_m_deqP_0_m_row_0_BITS_10_TO_6_1_m_row_1_B_ETC__q2 =
	      m_row_0[10:6];
      1'd1:
	  CASE_m_deqP_0_m_row_0_BITS_10_TO_6_1_m_row_1_B_ETC__q2 =
	      m_row_1[10:6];
    endcase
  end
  always@(m_deqP or m_row_0 or m_row_1)
  begin
    case (m_deqP)
      1'd0:
	  CASE_m_deqP_0_m_row_0_BITS_5_TO_0_1_m_row_1_BI_ETC__q3 =
	      m_row_0[5:0];
      1'd1:
	  CASE_m_deqP_0_m_row_0_BITS_5_TO_0_1_m_row_1_BI_ETC__q3 =
	      m_row_1[5:0];
    endcase
  end
  always@(m_deqP or m_row_0 or m_row_1)
  begin
    case (m_deqP)
      1'd0:
	  CASE_m_deqP_0_NOT_m_row_0_BIT_20_1_NOT_m_row_1_ETC__q4 =
	      !m_row_0[20];
      1'd1:
	  CASE_m_deqP_0_NOT_m_row_0_BIT_20_1_NOT_m_row_1_ETC__q4 =
	      !m_row_1[20];
    endcase
  end
  always@(m_deqP or m_row_0 or m_row_1)
  begin
    case (m_deqP)
      1'd0:
	  CASE_m_deqP_0_m_row_0_BITS_19_TO_13_1_m_row_1__ETC__q5 =
	      m_row_0[19:13];
      1'd1:
	  CASE_m_deqP_0_m_row_0_BITS_19_TO_13_1_m_row_1__ETC__q5 =
	      m_row_1[19:13];
    endcase
  end
  always@(m_deqP or m_row_0 or m_row_1)
  begin
    case (m_deqP)
      1'd0:
	  CASE_m_deqP_0_m_row_0_BIT_12_1_m_row_1_BIT_12__ETC__q6 =
	      m_row_0[12];
      1'd1:
	  CASE_m_deqP_0_m_row_0_BIT_12_1_m_row_1_BIT_12__ETC__q6 =
	      m_row_1[12];
    endcase
  end
  always@(m_deqP or m_row_0 or m_row_1)
  begin
    case (m_deqP)
      1'd0:
	  CASE_m_deqP_0_m_row_0_BIT_21_1_m_row_1_BIT_21__ETC__q7 =
	      m_row_0[21];
      1'd1:
	  CASE_m_deqP_0_m_row_0_BIT_21_1_m_row_1_BIT_21__ETC__q7 =
	      m_row_1[21];
    endcase
  end
  always@(m_deqP or m_row_0 or m_row_1)
  begin
    case (m_deqP)
      1'd0:
	  CASE_m_deqP_0_m_row_0_BITS_23_TO_22_1_m_row_1__ETC__q8 =
	      m_row_0[23:22];
      1'd1:
	  CASE_m_deqP_0_m_row_0_BITS_23_TO_22_1_m_row_1__ETC__q8 =
	      m_row_1[23:22];
    endcase
  end
  always@(m_deqP or m_specBits_0_rl or m_specBits_1_rl)
  begin
    case (m_deqP)
      1'd0:
	  CASE_m_deqP_0_m_specBits_0_rl_1_m_specBits_1_r_ETC__q9 =
	      m_specBits_0_rl;
      1'd1:
	  CASE_m_deqP_0_m_specBits_0_rl_1_m_specBits_1_r_ETC__q9 =
	      m_specBits_1_rl;
    endcase
  end

  // handling of inlined registers

  always@(posedge CLK)
  begin
    if (RST_N == `BSV_RESET_VALUE)
      begin
        m_deqP <= `BSV_ASSIGNMENT_DELAY 1'd0;
	m_enqP <= `BSV_ASSIGNMENT_DELAY 1'd0;
	m_poisoned_0_rl <= `BSV_ASSIGNMENT_DELAY 1'h0;
	m_poisoned_1_rl <= `BSV_ASSIGNMENT_DELAY 1'h0;
	m_specBits_0_rl <= `BSV_ASSIGNMENT_DELAY 12'hAAA;
	m_specBits_1_rl <= `BSV_ASSIGNMENT_DELAY 12'hAAA;
	m_valid_0_rl <= `BSV_ASSIGNMENT_DELAY 1'd0;
	m_valid_1_rl <= `BSV_ASSIGNMENT_DELAY 1'd0;
      end
    else
      begin
        if (m_deqP$EN) m_deqP <= `BSV_ASSIGNMENT_DELAY m_deqP$D_IN;
	if (m_enqP$EN) m_enqP <= `BSV_ASSIGNMENT_DELAY m_enqP$D_IN;
	if (m_poisoned_0_rl$EN)
	  m_poisoned_0_rl <= `BSV_ASSIGNMENT_DELAY m_poisoned_0_rl$D_IN;
	if (m_poisoned_1_rl$EN)
	  m_poisoned_1_rl <= `BSV_ASSIGNMENT_DELAY m_poisoned_1_rl$D_IN;
	if (m_specBits_0_rl$EN)
	  m_specBits_0_rl <= `BSV_ASSIGNMENT_DELAY m_specBits_0_rl$D_IN;
	if (m_specBits_1_rl$EN)
	  m_specBits_1_rl <= `BSV_ASSIGNMENT_DELAY m_specBits_1_rl$D_IN;
	if (m_valid_0_rl$EN)
	  m_valid_0_rl <= `BSV_ASSIGNMENT_DELAY m_valid_0_rl$D_IN;
	if (m_valid_1_rl$EN)
	  m_valid_1_rl <= `BSV_ASSIGNMENT_DELAY m_valid_1_rl$D_IN;
      end
    if (m_row_0$EN) m_row_0 <= `BSV_ASSIGNMENT_DELAY m_row_0$D_IN;
    if (m_row_1$EN) m_row_1 <= `BSV_ASSIGNMENT_DELAY m_row_1$D_IN;
  end

  // synopsys translate_off
  `ifdef BSV_NO_INITIAL_BLOCKS
  `else // not BSV_NO_INITIAL_BLOCKS
  initial
  begin
    m_deqP = 1'h0;
    m_enqP = 1'h0;
    m_poisoned_0_rl = 1'h0;
    m_poisoned_1_rl = 1'h0;
    m_row_0 = 24'hAAAAAA;
    m_row_1 = 24'hAAAAAA;
    m_specBits_0_rl = 12'hAAA;
    m_specBits_1_rl = 12'hAAA;
    m_valid_0_rl = 1'h0;
    m_valid_1_rl = 1'h0;
  end
  `endif // BSV_NO_INITIAL_BLOCKS
  // synopsys translate_on
endmodule  // mkDivExecQ

