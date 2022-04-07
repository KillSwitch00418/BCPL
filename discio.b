import "io"

manifest
{ iosb_ichar = 0;
  iosb_ochar = 1;
  iosb_close = 2;
  iosb_unit = 3;
  iosb_buffer = 4;
  iosb_pos = 5;
  iosb_size = 6;
  sizeof_iosb = 7;

  diosb_firstbn = 7;
  diosb_lastbn = 8;
  diosb_length = 9;
  diosb_de = 10;
  sizeof_diosb = 11;

  sb_rootdir_bn = 0;
  sb_first_free_bn = 1;
  sb_last_free_bn = 2;

  de_name = 0;
  de_first_bn = 5;
  de_last_bn = 6;
  de_length = 7;
  sizeof_de = 8;
  de_namelen = 5*4 - 1 }

let readch_tty(iosb) be
{ resultis inch() }

let writech_tty(iosb, c) be
{ outch(c) }

let close_tty(iosb) be
{ }

let tty = table readch_tty, writech_tty, close_tty, 0, 0, 0, 0;

let tapes = table 1, 0, 0, 0, 0, 0, 0, 0, 0;

let find_free_tape_unit() be
{ for i = 1 to 8 do
    if tapes ! i = 0 then
    { tapes ! i := 1;
      resultis i }
  out("All tape drives are in use\n");
  finish }

let close_writetape(iosb) be
{ let r;
  if iosb ! iosb_pos /= 0 then
  { let r = devctl(DC_TAPE_WRITE,
                   iosb ! iosb_unit, 
                   iosb ! iosb_buffer, 
                   iosb ! iosb_pos);
    if r < 0 then
    { out("code %d from tape write\n", r);
      finish } }
  r := devctl(DC_TAPE_UNLOAD, iosb ! iosb_unit);
  if r < 0 then
  { out("code %d from tape unload\n", r);
    finish }
  tapes ! (iosb ! iosb_unit) := 0;
  freevec(iosb ! iosb_buffer);
  freevec(iosb) }

let close_readtape(iosb) be
{ let r = devctl(DC_TAPE_UNLOAD, iosb ! iosb_unit);
  if r < 0 then
  { out("code %d from tape unload\n", r);
    finish }
  tapes ! (iosb ! iosb_unit) := 0;
  freevec(iosb ! iosb_buffer);
  freevec(iosb) }

let writechar_tape(iosb, ch) be
{ if iosb ! iosb_pos = iosb ! iosb_size then
  { let r = devctl(DC_TAPE_WRITE,
                   iosb ! iosb_unit, 
                   iosb ! iosb_buffer,
                   iosb ! iosb_size);
    if r < 0 then
    { out("code %d from tape write\n", r);
      finish }
    iosb ! iosb_pos := 0 }
  byte (iosb ! iosb_pos) of (iosb ! iosb_buffer) := ch;
  iosb ! iosb_pos +:= 1 }

let readchar_tape(iosb) be
{ let c;
  if iosb ! iosb_pos >= iosb ! iosb_size then
  { let r = devctl(DC_TAPE_READ,
                   iosb ! iosb_unit, 
                   iosb ! iosb_buffer);
    if r < 0 then
    { out("code %d from tape read\n", r);
      finish }
    iosb ! iosb_pos := 0;
    iosb ! iosb_size := r }
  if iosb ! iosb_pos = iosb ! iosb_size then
  { iosb ! iosb_size := -1;
    resultis -1; }
  c := byte (iosb ! iosb_pos) of (iosb ! iosb_buffer);
  iosb ! iosb_pos +:= 1;
  resultis c }

let illegal_writech(iosb, ch) be
{ out("Write performed on read-only file\n");
  finish }

let illegal_readch(iosb) be
{ out("Read performed on write-only file\n");
  finish }

let at_eof(iosb) be
{ resultis iosb ! iosb_size = -1 }

let tape_open_w(fname) be
{ let t = find_free_tape_unit();
  let r = devctl(DC_TAPE_LOAD, t, fname, 'W');
  if r < 0 then
  { out("code %d from tape load\n", r);
    finish }
  r := newvec(sizeof_iosb);
  r ! iosb_ichar := illegal_readch;
  r ! iosb_ochar := writechar_tape;
  r ! iosb_close := close_writetape;
  r ! iosb_unit := t;
  r ! iosb_buffer := newvec(128);
  r ! iosb_pos := 0;
  r ! iosb_size := 512;
  resultis r; }

let tape_open_r(fname) be
{ let t = find_free_tape_unit();
  let r = devctl(DC_TAPE_LOAD, t, fname, 'R');
  if r < 0 then
  { out("code %d from tape load\n", r);
    finish }
  r := newvec(sizeof_iosb);
  r ! iosb_ichar := readchar_tape;
  r ! iosb_ochar := illegal_writech;
  r ! iosb_close := close_readtape;
  r ! iosb_unit := t;
  r ! iosb_buffer := newvec(128);
  r ! iosb_pos := 0;
  r ! iosb_size := 512;
  resultis r; }

let stringeq(a, b) be
{ let i = 0;
  while true do
  { let ac = byte i of a, bc = byte i of b;
    if ac /= bc then
      resultis false;
    if ac = 0 then
      resultis true;
    i +:= 1 } }

let strncpy(dst, src, n) be
{ for i = 0 to n - 1 do
  { let c = byte i of src;
    byte i of dst := c;
    if c = 0 then
      return }
  byte (n - 1) of dst := 0 }

let superblock = nil;
let rootdir = nil;
let rootdirlen = 0;

let readblock(bn, addr) be
{ let r = devctl(DC_DISC_READ, 1, bn, 1, addr);
  if r < 0 then
  { out("Error %d from disc read\n", r);
    finish } }

let writeblock(bn, addr) be
{ let r = devctl(DC_DISC_WRITE, 1, bn, 1, addr);
  if r < 0 then
  { out("Error %d from disc write\n", r);
    finish } }

let disc_format() be
{ let r = devctl(DC_DISC_CHECK, 1), pos;
  if r <= 0 then
  { out("Error %d from disc 1\n", r);
    finish }
  test superblock = nil then
    superblock := newvec(128)
  else
  { out("disc is mounted, unmount first\n");
    return }
  superblock ! sb_rootdir_bn := 1;
  superblock ! sb_first_free_bn := 2;
  superblock ! sb_last_free_bn := r - 1;
  if rootdir = nil then
    rootdir := newvec(128);
  rootdirlen := 128;
  pos := 0;
  while pos < rootdirlen do
  { let de = rootdir + pos;
    de ! de_name := 0;
    pos +:= sizeof_de } }

let disc_mount() be
{ let r = devctl(DC_DISC_CHECK, 1);
  if r <= 0 then
  { out("Error %d from disc 1\n", r);
    finish }
  test superblock = nil then
    superblock := newvec(128)
  else
  { out("disc is mounted, unmount first\n");
    return }
  readblock(0, superblock);
  if rootdir = nil then
    rootdir := newvec(128);
  rootdirlen := 128;
  readblock(superblock ! sb_rootdir_bn, rootdir) }

let disc_save_all() be
{ if superblock = nil then
  { out("disc is not mounted\n");
    return }
  writeblock(0, superblock);
  writeblock(superblock ! sb_rootdir_bn, rootdir) }

let disc_unmount() be
{ if superblock = nil then
  { out("disc has not been mounted\n");
    return }
  disc_save_all();
  freevec(superblock);
  superblock := nil;
  freevec(rootdir);
  rootdir := nil;
  rootdirlen := 0 }

let disc_readch(iosb) be
{
  let ch = 0;
  if iosb ! iosb_pos >= iosb ! iosb_size then
  {
    if iosb ! diosb_firstbn <= iosb ! diosb_lastbn then
    {
      readblock(iosb ! diosb_firstbn, iosb ! iosb_buffer);
      iosb ! diosb_firstbn +:=1;
      iosb ! diosb_length +:= iosb! diosb_lastbn;
    }
    iosb ! iosb_pos := 0;
    iosb ! iosb_size := iosb ! diosb_length
  }
  if iosb ! diosb_firstbn = iosb ! diosb_lastbn then
  {
    iosb ! iosb_size := -1;
    resultis -1;
  }
  ch := (byte iosb ! iosb_pos)of(iosb ! iosb_buffer);
  iosb! ! iosb_pos +:= 1;
  resultis ch;
}

let disc_writech(iosb, ch) be
{ if iosb ! iosb_pos >= iosb ! iosb_size then
  { if iosb ! diosb_firstbn <= iosb ! diosb_lastbn then
    { writeblock(iosb ! diosb_firstbn, iosb ! iosb_buffer);
      iosb ! diosb_firstbn +:= 1;
      iosb ! diosb_length +:= 512 }   
    iosb ! iosb_pos := 0;
    iosb ! iosb_size := 512 }
  byte (iosb ! iosb_pos) of (iosb ! iosb_buffer) := ch;
  iosb ! iosb_pos +:= 1 }

let disc_close_r(iosb) be
{
  freevec(iosb ! iosb_buffer);
  freevec(iosb)
}

let disc_close_w(iosb) be
{ if iosb ! iosb_pos > 0 then
  { if iosb ! diosb_firstbn <= iosb ! diosb_lastbn then
    { writeblock(iosb ! diosb_firstbn, iosb ! iosb_buffer);
      iosb ! diosb_length +:= iosb ! iosb_pos } }
  iosb ! diosb_de ! de_length := iosb ! diosb_length;
  freevec(iosb ! iosb_buffer);
  freevec(iosb) }

let disc_find_file(name) be
{ let pos = 0;
  if rootdir = nil then
    resultis nil;
  while pos < rootdirlen do
  { let de = rootdir + pos;
    if stringeq(name, de + de_name) then
      resultis de;
    pos +:= sizeof_de }
  resultis nil }

let disc_create_file(name, nb) be
{ let b1 = superblock ! sb_first_free_bn;
  let bn = b1 + nb - 1;
  let pos = 0;
  if rootdir = nil then
    resultis nil;
  if bn > superblock ! sb_last_free_bn then
    resultis nil;
  while pos < rootdirlen do
  { let de = rootdir + pos;
    if de ! de_name = 0 then
    { strncpy(de + de_name, name, de_namelen);
      de ! de_first_bn := b1;
      de ! de_last_bn := bn;
      de ! de_length := 0;
      superblock ! sb_first_free_bn +:= nb;
      resultis de }
    pos +:= sizeof_de }
  resultis nil }

let disc_delete_file(name) be
{ let pos = 0;
  if rootdir = nil then
    resultis false;
  while pos < rootdirlen do
  { let de = rootdir + pos;
    if stringeq(name, de + de_name) then
    { de ! de_name := 0;
      resultis true }
    pos +:= sizeof_de }
  resultis false }

let disc_open_new_file(name, maxlen) be
{ let blocks = (maxlen + 511) / 512;
  let de = disc_create_file(name, blocks);
  let r;
  if de = nil then
    resultis nil;
  r := newvec(sizeof_diosb);
  r ! iosb_ichar := illegal_readch;
  r ! iosb_ochar := disc_writech;
  r ! iosb_close := disc_close_w;
  r ! iosb_buffer := newvec(128);
  r ! iosb_pos := 0;
  r ! iosb_size := 512;
  r ! diosb_firstbn := de ! de_first_bn;
  r ! diosb_lastbn := de ! de_last_bn;
  r ! diosb_length := 0;
  r ! diosb_de := de;
  resultis r }

let disc_open_file_write(name) be
{ let de = disc_find_file(name);
  let r;
  if de = nil then
    resultis nil;
  r := newvec(sizeof_diosb);
  r ! iosb_ichar := illegal_readch;
  r ! iosb_ochar := disc_writech;
  r ! iosb_close := disc_close_w;
  r ! iosb_buffer := newvec(128);
  r ! iosb_pos := 0;
  r ! iosb_size := 512;
  r ! diosb_firstbn := de ! de_first_bn;
  r ! diosb_lastbn := de ! de_last_bn;
  r ! diosb_length := 0;
  r ! diosb_de := de;
  resultis r }

let disc_open_file_read(name) be
{ 
  let de = disc_find_file(name);
  let r;
  if de = nil then
    resultis nil;
  r := newvec(sizeof_diosb);
  r ! iosb_ichar := disc_readch;
  r ! iosb_ochar := illegal_writech;
  r ! iosb_close := disc_close_r;
  r ! iosb_buffer := newvec(128);
  r ! iosb_pos := 0;
  r ! iosb_size := 0;
  r ! diosb_firstbn := de ! de_first_bn;
  r ! diosb_lastbn := de ! de_last_bn;
  r ! diosb_length := de ! de_length;
  r ! diosb_de := de;
  resultis r 
}

let disc_listdir() be
{ let pos = 0;
  if rootdir = nil then
    return;
  while pos < rootdirlen do
  { let de = rootdir + pos;
    test de ! de_name = 0 then
      out("(unused)\n")
    else
      out("%s: first block = %d, last_block = %d, length = %d\n",
          de + de_name, de ! de_first_bn, de ! de_last_bn, de ! de_length);
    pos +:= sizeof_de } }

let writech(iosb, ch) be
{ if iosb = nil then
  { out("writech: iosb is nil\n");
    return }
  (iosb ! iosb_ochar)(iosb, ch) }

let readch(iosb) be
{ if iosb = nil then
  { out("readch: iosb is nil\n");
    resultis -1 }
  resultis (iosb ! iosb_ichar)(iosb) }

let close(iosb) be
{ if iosb = nil then
  { out("close: iosb is nil\n");
    return }
  (iosb ! iosb_close)(iosb) }

let writestr(iosb, s) be
{ let i = 0;
  while true do
  { let c = byte i of s;
    if c = 0 then break;
    writech(iosb, c);
    i +:= 1 } }

let readstr(iosb, s, max) be
{ let pos = 0;
  while pos < max do
  { let c = readch(iosb);
    if c < ' ' then break;
    byte pos of s := c;
    pos +:= 1 }
  byte pos of s := 0 }

let writeno(iosb, n) be
{ if n < 0 then
  { writech(iosb, '-');
    n := -n }
  if n > 9 then
    writeno(iosb, n / 10);
  writech(iosb, '0' + n rem 10) }

let readno(iosb) be
{ let n = 0, c = readch(iosb), s = 1;
  while c < ' ' do
    c:=readch(iosb);
  if c = '-' then
  { s := -1;
    c := readch(iosb) }
  while c >= '0' /\ c <= '9' do
  { n := n * 10 + c - '0'; 
    c := readch(iosb) }
  resultis n * s }

// test of tape system
let test_tape() be
{ let fi, fo, min, max;
  writestr(tty, "The program is creating table.txt\n");
  fi := tape_open_r("limits.txt");
  fo := tape_open_w("table.txt");
  // I should check to see if fi or fo are nil.
  min := readno(fi);
  max := readno(fi);
  for cent = min to max do
  { let fahr = cent * 9 / 5 + 32;
    writeno(fo, cent);
    writestr(fo, " centigrade is ");
    writeno(fo, fahr);
    writestr(fo, " fahrenheit\n") }
  close(fi);
  close(fo) }

// basic test of disc system write
let test_make_table() be
{ let fo = disc_open_new_file("table.txt", 3500);
  // I should check to see if fo is nil.
  writestr(fo, "abcdefghijklmnopqrstuvwxyz\n");
  for cent = 0 to 100 do
  { let fahr = cent * 9 / 5 + 32;
    writeno(fo, cent);
    writestr(fo, " centigrade is ");
    writeno(fo, fahr);
    writestr(fo, " fahrenheit\n") }
  close(fo) }

let test_create_any_file() be
{ let fo, fname = vec(10), len;
  writestr(tty, "Enter file name: ");
  readstr(tty, fname, 39);
  writestr(tty, "Maximum length (in bytes): ");
  len := inno();
  fo := disc_open_new_file(fname, len);
  // I should check to see if fo is nil.
  writestr(tty, "Enter content, end with *:\n");
  while true do
  { let c = readch(tty);
    if c = '*' then break;
    writech(fo, c) }
  while true do
  { let c = readch(tty);
    if c = '\n' then break }
  close(fo) }

let test_read_any_file() be
{ let fi, fname = vec(10);
  writestr(tty, "Enter file name: ");
  readstr(tty, fname, 39);
  fi := disc_open_file_read(fname);
  // I should check to see if fi is nil.
  while true do
  { let c = readch(fi);
    if c = -1 then break;
    writech(tty, c) } }

let test_delete_file() be
{ let fname = vec(10);
  writestr(tty, "Enter file name: ");
  readstr(tty, fname, 39);
  disc_delete_file(fname)
  /* I should check that the result is not false */ }

let start() be
{ let line = vec(10);
  init(!0x101, !0x100 - !0x101);
  writestr(tty, "Remember to mount or format first\nAnd unmount when you're done\n\n");
  while true do
  { writestr(tty, "1: tape test\n");
    writestr(tty, "2: format disc\n");
    writestr(tty, "3: mount disc\n");
    writestr(tty, "4: unmount disc\n");
    writestr(tty, "5: list directory\n");
    writestr(tty, "6: create table.txt\n");
    writestr(tty, "7: create any file\n");
    writestr(tty, "8: read any file\n");
    writestr(tty, "9: delete a file\n");
    writestr(tty, "x: exit\n");
    writestr(tty, "? ");
    readstr(tty, line, 39);
    switchon line ! 0 into
    { case '1':
        test_tape();
        endcase;
      case '2':
        disc_format();
        endcase;
      case '3':
        disc_mount();
        endcase;
      case '4':
        disc_unmount();
        endcase;
      case '5':
        disc_listdir();
        endcase;
      case '6':
        test_make_table();
        endcase;
      case '7':
        test_create_any_file();
        endcase;
      case '8':
        test_read_any_file();
        endcase;
      case '9':
        test_delete_file();
        endcase;
      case 'x':
        finish;
      case '\n':
        endcase;
      default:
        out("You typed \"%s\"\nWhat?\n", line); } } }
