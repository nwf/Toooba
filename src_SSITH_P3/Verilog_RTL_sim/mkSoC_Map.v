//
// Generated by Bluespec Compiler, version 2019.05.beta2 (build a88bf40db, 2019-05-24)
//
// On Thu Jul  2 02:46:47 BST 2020
//
//
// Ports:
// Name                         I/O  size props
// m_plic_addr_range              O   128 const
// m_near_mem_io_addr_range       O   128 const
// m_flash_mem_addr_range         O   128 const
// m_ethernet_0_addr_range        O   128 const
// m_dma_0_addr_range             O   128 const
// m_uart16550_0_addr_range       O   128 const
// m_gpio_0_addr_range            O   128 const
// m_boot_rom_addr_range          O   128 const
// m_ddr4_0_uncached_addr_range   O   128 const
// m_ddr4_0_cached_addr_range     O   128 const
// m_mem0_controller_addr_range   O   128 const
// m_is_mem_addr                  O     1
// m_is_IO_addr                   O     1
// m_is_near_mem_IO_addr          O     1
// m_pc_reset_value               O    64 const
// m_mtvec_reset_value            O    64 const
// m_nmivec_reset_value           O    64 const
// CLK                            I     1 unused
// RST_N                          I     1 unused
// m_is_mem_addr_addr             I    64
// m_is_IO_addr_addr              I    64
// m_is_near_mem_IO_addr_addr     I    64
//
// Combinational paths from inputs to outputs:
//   m_is_mem_addr_addr -> m_is_mem_addr
//   m_is_IO_addr_addr -> m_is_IO_addr
//   m_is_near_mem_IO_addr_addr -> m_is_near_mem_IO_addr
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

module mkSoC_Map(CLK,
		 RST_N,

		 m_plic_addr_range,

		 m_near_mem_io_addr_range,

		 m_flash_mem_addr_range,

		 m_ethernet_0_addr_range,

		 m_dma_0_addr_range,

		 m_uart16550_0_addr_range,

		 m_gpio_0_addr_range,

		 m_boot_rom_addr_range,

		 m_ddr4_0_uncached_addr_range,

		 m_ddr4_0_cached_addr_range,

		 m_mem0_controller_addr_range,

		 m_is_mem_addr_addr,
		 m_is_mem_addr,

		 m_is_IO_addr_addr,
		 m_is_IO_addr,

		 m_is_near_mem_IO_addr_addr,
		 m_is_near_mem_IO_addr,

		 m_pc_reset_value,

		 m_mtvec_reset_value,

		 m_nmivec_reset_value);
  input  CLK;
  input  RST_N;

  // value method m_plic_addr_range
  output [127 : 0] m_plic_addr_range;

  // value method m_near_mem_io_addr_range
  output [127 : 0] m_near_mem_io_addr_range;

  // value method m_flash_mem_addr_range
  output [127 : 0] m_flash_mem_addr_range;

  // value method m_ethernet_0_addr_range
  output [127 : 0] m_ethernet_0_addr_range;

  // value method m_dma_0_addr_range
  output [127 : 0] m_dma_0_addr_range;

  // value method m_uart16550_0_addr_range
  output [127 : 0] m_uart16550_0_addr_range;

  // value method m_gpio_0_addr_range
  output [127 : 0] m_gpio_0_addr_range;

  // value method m_boot_rom_addr_range
  output [127 : 0] m_boot_rom_addr_range;

  // value method m_ddr4_0_uncached_addr_range
  output [127 : 0] m_ddr4_0_uncached_addr_range;

  // value method m_ddr4_0_cached_addr_range
  output [127 : 0] m_ddr4_0_cached_addr_range;

  // value method m_mem0_controller_addr_range
  output [127 : 0] m_mem0_controller_addr_range;

  // value method m_is_mem_addr
  input  [63 : 0] m_is_mem_addr_addr;
  output m_is_mem_addr;

  // value method m_is_IO_addr
  input  [63 : 0] m_is_IO_addr_addr;
  output m_is_IO_addr;

  // value method m_is_near_mem_IO_addr
  input  [63 : 0] m_is_near_mem_IO_addr_addr;
  output m_is_near_mem_IO_addr;

  // value method m_pc_reset_value
  output [63 : 0] m_pc_reset_value;

  // value method m_mtvec_reset_value
  output [63 : 0] m_mtvec_reset_value;

  // value method m_nmivec_reset_value
  output [63 : 0] m_nmivec_reset_value;

  // signals for module outputs
  wire [127 : 0] m_boot_rom_addr_range,
		 m_ddr4_0_cached_addr_range,
		 m_ddr4_0_uncached_addr_range,
		 m_dma_0_addr_range,
		 m_ethernet_0_addr_range,
		 m_flash_mem_addr_range,
		 m_gpio_0_addr_range,
		 m_mem0_controller_addr_range,
		 m_near_mem_io_addr_range,
		 m_plic_addr_range,
		 m_uart16550_0_addr_range;
  wire [63 : 0] m_mtvec_reset_value, m_nmivec_reset_value, m_pc_reset_value;
  wire m_is_IO_addr, m_is_mem_addr, m_is_near_mem_IO_addr;

  // remaining internal signals
  wire [63 : 0] x__h181,
		x__h205,
		x__h229,
		x__h254,
		x__h279,
		x__h304,
		x__h329,
		x__h354,
		x__h379,
		x__h404,
		x__h656;
  wire NOT_m_is_IO_addr_addr_ULT_0x62300000_4___d35,
       NOT_m_is_IO_addr_addr_ULT_0xC000000_AND_m_is_I_ETC___d21,
       NOT_m_is_IO_addr_addr_ULT_0xC000000_AND_m_is_I_ETC___d33,
       NOT_m_is_IO_addr_addr_ULT_0xC000000_AND_m_is_I_ETC___d45,
       NOT_m_is_IO_addr_addr_ULT_0xC000000_AND_m_is_I_ETC___d57,
       NOT_m_is_IO_addr_addr_ULT_0xC000000_AND_m_is_I_ETC___d95,
       m_is_IO_addr_addr_ULT_0x30000000___d93,
       m_is_IO_addr_addr_ULT_1073741824___d16;

  // value method m_plic_addr_range
  assign m_plic_addr_range = 128'h000000000C0000000000000000400000 ;

  // value method m_near_mem_io_addr_range
  assign m_near_mem_io_addr_range = 128'h00000000100000000000000000010000 ;

  // value method m_flash_mem_addr_range
  assign m_flash_mem_addr_range = 128'h00000000400000000000000008000000 ;

  // value method m_ethernet_0_addr_range
  assign m_ethernet_0_addr_range = 128'h00000000621000000000000000040000 ;

  // value method m_dma_0_addr_range
  assign m_dma_0_addr_range = 128'h00000000622000000000000000010000 ;

  // value method m_uart16550_0_addr_range
  assign m_uart16550_0_addr_range = 128'h00000000623000000000000000001000 ;

  // value method m_gpio_0_addr_range
  assign m_gpio_0_addr_range = 128'h000000006FFF00000000000000010000 ;

  // value method m_boot_rom_addr_range
  assign m_boot_rom_addr_range = 128'h00000000700000000000000000001000 ;

  // value method m_ddr4_0_uncached_addr_range
  assign m_ddr4_0_uncached_addr_range =
	     128'h00000000800000000000000040000000 ;

  // value method m_ddr4_0_cached_addr_range
  assign m_ddr4_0_cached_addr_range = 128'h00000000C00000000000000040000000 ;

  // value method m_mem0_controller_addr_range
  assign m_mem0_controller_addr_range =
	     128'h00000000C00000000000000040000000 ;

  // value method m_is_mem_addr
  assign m_is_mem_addr =
	     m_is_mem_addr_addr >= 64'h00000000C0000000 &&
	     x__h181 < 64'h0000000040000000 ;

  // value method m_is_IO_addr
  assign m_is_IO_addr =
	     NOT_m_is_IO_addr_addr_ULT_0xC000000_AND_m_is_I_ETC___d95 ||
	     !m_is_IO_addr_addr_ULT_0x30000000___d93 &&
	     m_is_IO_addr_addr_ULT_1073741824___d16 ;

  // value method m_is_near_mem_IO_addr
  assign m_is_near_mem_IO_addr =
	     m_is_near_mem_IO_addr_addr >= 64'h0000000010000000 &&
	     x__h656 < 64'h0000000000010000 ;

  // value method m_pc_reset_value
  assign m_pc_reset_value = 64'h0000000070000000 ;

  // value method m_mtvec_reset_value
  assign m_mtvec_reset_value = 64'h0000000000001000 ;

  // value method m_nmivec_reset_value
  assign m_nmivec_reset_value = 64'hAAAAAAAAAAAAAAAA ;

  // remaining internal signals
  assign NOT_m_is_IO_addr_addr_ULT_0x62300000_4___d35 =
	     m_is_IO_addr_addr >= 64'h0000000062300000 ;
  assign NOT_m_is_IO_addr_addr_ULT_0xC000000_AND_m_is_I_ETC___d21 =
	     m_is_IO_addr_addr >= 64'h000000000C000000 &&
	     x__h205 < 64'h0000000000400000 ||
	     m_is_IO_addr_addr >= 64'h0000000010000000 &&
	     x__h229 < 64'h0000000000010000 ||
	     !m_is_IO_addr_addr_ULT_1073741824___d16 &&
	     x__h254 < 64'h0000000008000000 ;
  assign NOT_m_is_IO_addr_addr_ULT_0xC000000_AND_m_is_I_ETC___d33 =
	     NOT_m_is_IO_addr_addr_ULT_0xC000000_AND_m_is_I_ETC___d21 ||
	     m_is_IO_addr_addr >= 64'h0000000062100000 &&
	     x__h279 < 64'h0000000000040000 ||
	     m_is_IO_addr_addr >= 64'h0000000062200000 &&
	     x__h304 < 64'h0000000000010000 ;
  assign NOT_m_is_IO_addr_addr_ULT_0xC000000_AND_m_is_I_ETC___d45 =
	     NOT_m_is_IO_addr_addr_ULT_0xC000000_AND_m_is_I_ETC___d33 ||
	     NOT_m_is_IO_addr_addr_ULT_0x62300000_4___d35 &&
	     x__h329 < 64'h0000000000001000 ||
	     m_is_IO_addr_addr >= 64'h000000006FFF0000 &&
	     x__h354 < 64'h0000000000010000 ;
  assign NOT_m_is_IO_addr_addr_ULT_0xC000000_AND_m_is_I_ETC___d57 =
	     NOT_m_is_IO_addr_addr_ULT_0xC000000_AND_m_is_I_ETC___d45 ||
	     m_is_IO_addr_addr >= 64'h0000000070000000 &&
	     x__h379 < 64'h0000000000001000 ||
	     m_is_IO_addr_addr >= 64'h0000000080000000 &&
	     x__h404 < 64'h0000000040000000 ;
  assign NOT_m_is_IO_addr_addr_ULT_0xC000000_AND_m_is_I_ETC___d95 =
	     NOT_m_is_IO_addr_addr_ULT_0xC000000_AND_m_is_I_ETC___d57 ||
	     m_is_IO_addr_addr >= 64'h0000000062400000 &&
	     m_is_IO_addr_addr < 64'd1648365568 ||
	     NOT_m_is_IO_addr_addr_ULT_0x62300000_4___d35 &&
	     m_is_IO_addr_addr < 64'd1647316992 ||
	     m_is_IO_addr_addr >= 64'h0000000062310000 &&
	     m_is_IO_addr_addr < 64'd1647382528 ||
	     m_is_IO_addr_addr >= 64'h0000000062320000 &&
	     m_is_IO_addr_addr < 64'd1647448064 ||
	     m_is_IO_addr_addr >= 64'h0000000062360000 &&
	     m_is_IO_addr_addr < 64'd1647710208 ||
	     m_is_IO_addr_addr >= 64'h0000000062330000 &&
	     m_is_IO_addr_addr < 64'd1647513600 ||
	     m_is_IO_addr_addr >= 64'h0000000062370000 &&
	     m_is_IO_addr_addr < 64'd1647775744 ||
	     m_is_IO_addr_addr >= 64'h0000000020000000 &&
	     m_is_IO_addr_addr_ULT_0x30000000___d93 ;
  assign m_is_IO_addr_addr_ULT_0x30000000___d93 =
	     m_is_IO_addr_addr < 64'h0000000030000000 ;
  assign m_is_IO_addr_addr_ULT_1073741824___d16 =
	     m_is_IO_addr_addr < 64'd1073741824 ;
  assign x__h181 = m_is_mem_addr_addr - 64'h00000000C0000000 ;
  assign x__h205 = m_is_IO_addr_addr - 64'h000000000C000000 ;
  assign x__h229 = m_is_IO_addr_addr - 64'h0000000010000000 ;
  assign x__h254 = m_is_IO_addr_addr - 64'h0000000040000000 ;
  assign x__h279 = m_is_IO_addr_addr - 64'h0000000062100000 ;
  assign x__h304 = m_is_IO_addr_addr - 64'h0000000062200000 ;
  assign x__h329 = m_is_IO_addr_addr - 64'h0000000062300000 ;
  assign x__h354 = m_is_IO_addr_addr - 64'h000000006FFF0000 ;
  assign x__h379 = m_is_IO_addr_addr - 64'h0000000070000000 ;
  assign x__h404 = m_is_IO_addr_addr - 64'h0000000080000000 ;
  assign x__h656 = m_is_near_mem_IO_addr_addr - 64'h0000000010000000 ;
endmodule  // mkSoC_Map

