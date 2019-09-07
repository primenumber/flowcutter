struct Config {
    pub filename: String,
    pub target: String,
    pub frequency: usize,
}

#[derive(Debug)]
enum Instruction {
    Input,
    Add(usize, usize),
    Sub(usize, usize),
    Negate(usize),
    UMul(usize, usize), // Unsigned multiplie
    SMul(usize, usize), // Signed multiplie
    And(usize, usize), // Bitwise and
    AndAll(usize), // Bitwise and reduction
    Or(usize, usize), // Bitwise or
    OrAll(usize), // Bitwise or reduction
    Xor(usize, usize), // Bitwise xor
    XorAll(usize), // Bitwise xor reduction
    Not(usize), // Bitwise not
    Sll(usize, usize), // Shift logical left
    Slr(usize, usize), // Shift logical right
    Sar(usize, usize), // Shift arithmetic right
    Equal(usize, usize),
    ULess(usize, usize), // Unsigned less
    SLess(usize, usize), // Signed less
    ULessOrEqual(usize, usize), // Unsigned less or equal
    SLessOrEqual(usize, usize), // Signed less or equal
    UGreater(usize, usize), // Unsigned greater
    SGreater(usize, usize), // Signed greater
    UGreaterOrEqual(usize, usize), // Unsigned greater or equal
    SGreaterOrEqual(usize, usize), // Signed greater or equal
    Mux(usize, usize, usize), // Multiplexer
    Ext(usize, usize, usize), // Extract bits
    Cat(usize, usize), // Concat bits
    Const(Vec<bool>), // Constant
    Id(usize), // Identity
}

#[derive(Debug, Clone)]
struct Variable {
    id: usize,
    width: usize,
}

#[macro_use] extern crate failure;

#[derive(Debug, Fail)]
enum ParseIRError {
    #[fail(display = "Not enough arguments")]
    NotEnoughArgumentError,
    #[fail(display = "Undefined variable: {}", token)]
    UndefinedVariableError{ token: String },
    #[fail(display = "Expected variable: {}", token)]
    ParseVariableError{ token: String },
    #[fail(display = "Expected constant: {}", token)]
    ParseBitsError{ token: String },
    #[fail(display = "Unknown operator: {}", token)]
    UnknownOperatorError{ token: String },
}

fn parse_variable(token: &str, id: usize) -> Result<usize, failure::Error> {
    if token.len() < 2 {
        return Err(failure::Error::from(ParseIRError::ParseVariableError{ token: token.to_string() }));
    }
    if token.chars().nth(0) != Some('%') {
        return Err(failure::Error::from(ParseIRError::ParseVariableError{ token: token.to_string() }));
    }
    let num = token[1..].parse()?;
    if num >= id {
        return Err(failure::Error::from(ParseIRError::UndefinedVariableError{ token: token.to_string() }));
    }
    Ok(num)
}

fn parse_bits(token: &str) -> Result<Vec<bool>, failure::Error> {
    let mut res = Vec::<bool>::new();
    for ch in token.chars().rev() {
        match ch.to_digit(16) {
            Some(hex) => {
                for i in 0..4 {
                    res.push(((hex >> i) & 1u32) == 1);
                }
            },
            None => return Err(failure::Error::from(ParseIRError::ParseBitsError{ token: token.to_string() }))
        }
    }
    Ok(res)
}

fn parse_line(line: &str) -> Result<(Variable, Instruction), failure::Error> {
    let tokens = line.split_whitespace().collect::<Vec<&str>>();
    if tokens.len() < 3 {
        return Err(failure::Error::from(ParseIRError::NotEnoughArgumentError));
    }
    let id: usize = parse_variable(tokens[0], usize::max_value())?;
    let width: usize = tokens[1].parse()?;
    match tokens[2] {
        "input" => {
            Ok((Variable{ id, width }, Instruction::Input))
        },
        "add" => {
            let lhsnum = parse_variable(tokens[3], id)?;
            let rhsnum = parse_variable(tokens[4], id)?;
            Ok((Variable{ id, width }, Instruction::Add(lhsnum, rhsnum)))
        },
        "sub" => {
            let lhsnum = parse_variable(tokens[3], id)?;
            let rhsnum = parse_variable(tokens[4], id)?;
            Ok((Variable{ id, width }, Instruction::Sub(lhsnum, rhsnum)))
        },
        "neg" => {
            let num: usize = parse_variable(tokens[3], id)?;
            Ok((Variable{ id, width }, Instruction::Negate(num)))
        },
        "umul" => {
            let lhsnum = parse_variable(tokens[3], id)?;
            let rhsnum = parse_variable(tokens[4], id)?;
            Ok((Variable{ id, width }, Instruction::UMul(lhsnum, rhsnum)))
        },
        "smul" => {
            let lhsnum = parse_variable(tokens[3], id)?;
            let rhsnum = parse_variable(tokens[4], id)?;
            Ok((Variable{ id, width }, Instruction::SMul(lhsnum, rhsnum)))
        },
        "and" => {
            let lhsnum = parse_variable(tokens[3], id)?;
            let rhsnum = parse_variable(tokens[4], id)?;
            Ok((Variable{ id, width }, Instruction::And(lhsnum, rhsnum)))
        },
        "andall" => {
            let num: usize = parse_variable(tokens[3], id)?;
            Ok((Variable{ id, width }, Instruction::AndAll(num)))
        },
        "or" => {
            let lhsnum = parse_variable(tokens[3], id)?;
            let rhsnum = parse_variable(tokens[4], id)?;
            Ok((Variable{ id, width }, Instruction::Or(lhsnum, rhsnum)))
        },
        "orall" => {
            let num: usize = parse_variable(tokens[3], id)?;
            Ok((Variable{ id, width }, Instruction::OrAll(num)))
        },
        "xor" => {
            let lhsnum = parse_variable(tokens[3], id)?;
            let rhsnum = parse_variable(tokens[4], id)?;
            Ok((Variable{ id, width }, Instruction::Xor(lhsnum, rhsnum)))
        },
        "xorall" => {
            let num: usize = parse_variable(tokens[3], id)?;
            Ok((Variable{ id, width }, Instruction::XorAll(num)))
        },
        "not" => {
            let num: usize = parse_variable(tokens[3], id)?;
            Ok((Variable{ id, width }, Instruction::Not(num)))
        },
        "sll" => {
            let lhsnum = parse_variable(tokens[3], id)?;
            let rhsnum = parse_variable(tokens[4], id)?;
            Ok((Variable{ id, width }, Instruction::Sll(lhsnum, rhsnum)))
        },
        "slr" => {
            let lhsnum = parse_variable(tokens[3], id)?;
            let rhsnum = parse_variable(tokens[4], id)?;
            Ok((Variable{ id, width }, Instruction::Slr(lhsnum, rhsnum)))
        },
        "sar" => {
            let lhsnum = parse_variable(tokens[3], id)?;
            let rhsnum = parse_variable(tokens[4], id)?;
            Ok((Variable{ id, width }, Instruction::Sar(lhsnum, rhsnum)))
        },
        "eq" => {
            let lhsnum = parse_variable(tokens[3], id)?;
            let rhsnum = parse_variable(tokens[4], id)?;
            Ok((Variable{ id, width }, Instruction::Equal(lhsnum, rhsnum)))
        },
        "uless" => {
            let lhsnum = parse_variable(tokens[3], id)?;
            let rhsnum = parse_variable(tokens[4], id)?;
            Ok((Variable{ id, width }, Instruction::ULess(lhsnum, rhsnum)))
        },
        "sless" => {
            let lhsnum = parse_variable(tokens[3], id)?;
            let rhsnum = parse_variable(tokens[4], id)?;
            Ok((Variable{ id, width }, Instruction::SLess(lhsnum, rhsnum)))
        },
        "uleq" => {
            let lhsnum = parse_variable(tokens[3], id)?;
            let rhsnum = parse_variable(tokens[4], id)?;
            Ok((Variable{ id, width }, Instruction::ULessOrEqual(lhsnum, rhsnum)))
        },
        "sleq" => {
            let lhsnum = parse_variable(tokens[3], id)?;
            let rhsnum = parse_variable(tokens[4], id)?;
            Ok((Variable{ id, width }, Instruction::SLessOrEqual(lhsnum, rhsnum)))
        },
        "ugr" => {
            let lhsnum = parse_variable(tokens[3], id)?;
            let rhsnum = parse_variable(tokens[4], id)?;
            Ok((Variable{ id, width }, Instruction::UGreater(lhsnum, rhsnum)))
        },
        "sgr" => {
            let lhsnum = parse_variable(tokens[3], id)?;
            let rhsnum = parse_variable(tokens[4], id)?;
            Ok((Variable{ id, width }, Instruction::SGreater(lhsnum, rhsnum)))
        },
        "ugeq" => {
            let lhsnum = parse_variable(tokens[3], id)?;
            let rhsnum = parse_variable(tokens[4], id)?;
            Ok((Variable{ id, width }, Instruction::UGreaterOrEqual(lhsnum, rhsnum)))
        },
        "sgeq" => {
            let lhsnum = parse_variable(tokens[3], id)?;
            let rhsnum = parse_variable(tokens[4], id)?;
            Ok((Variable{ id, width }, Instruction::SGreaterOrEqual(lhsnum, rhsnum)))
        },
        "mux" => {
            let condnum: usize = parse_variable(tokens[3], id)?;
            let lhsnum = parse_variable(tokens[4], id)?;
            let rhsnum = parse_variable(tokens[5], id)?;
            Ok((Variable{ id, width }, Instruction::Mux(condnum, lhsnum, rhsnum)))
        },
        "ext" => {
            let num: usize = parse_variable(tokens[3], id)?;
            let start: usize = tokens[4].parse()?;
            let end: usize = tokens[5].parse()?;
            Ok((Variable{ id, width }, Instruction::Ext(num, start, end)))
        },
        "cat" => {
            let lhsnum = parse_variable(tokens[3], id)?;
            let rhsnum = parse_variable(tokens[4], id)?;
            Ok((Variable{ id, width }, Instruction::Cat(lhsnum, rhsnum)))
        },
        "const" => {
            let bits: Vec<bool> = parse_bits(tokens[3])?;
            Ok((Variable{ id, width }, Instruction::Const(bits)))
        },
        "id" => {
            let num: usize = parse_variable(tokens[3], id)?;
            Ok((Variable{ id, width }, Instruction::Id(num)))
        },
        op => Err(failure::Error::from(ParseIRError::UnknownOperatorError{ token: op.to_string() }))
    }
}

use std::fs::File;
use std::io::{Write, BufRead, BufReader};

fn parse(filename: &str) -> Result<Vec<(Variable, Instruction)>, failure::Error> {
    let file = File::open(filename)?;
    let mut res = Vec::new();
    for line in BufReader::new(file).lines() {
        res.push(parse_line(&line.unwrap())?);
    }
    Ok(res)
}

#[derive(Debug, Clone)]
enum Element {
    Input,
    FAdd(usize, usize, usize),
    LUT6(u64, [usize; 6]),
    Mul48(usize, usize),
    Ext(usize, usize, usize),
    Cat(usize, usize),
    Const(bool),
}

use std::collections::HashMap;

fn ext_bits(ids: &[usize], res: &mut Vec<(Variable, Element)>, count: &mut usize) -> Vec<usize> {
    let mut ext_ids = Vec::new();
    for id in ids {
        let w = res[*id].0.width;
        if w == 1 {
            ext_ids.push(*id);
        } else {
            for i in 0..w {
                res.push((Variable { id: *count, width: 1 },
                          Element::Ext(*id, i, i+1)));
                ext_ids.push(*count);
                *count += 1;
            }
        }
    }
    ext_ids
}

fn cat_bits(ids: &[usize], res: &mut Vec<(Variable, Element)>, count: &mut usize) -> usize {
    let mut old = 0;
    let mut w = 0;
    for (i, id) in ids.iter().enumerate() {
        if i == 0 {
            old = *id;
            w = res[*id].0.width;
        } else {
            w += res[*id].0.width;
            res.push((Variable { id: *count, width: w },
                      Element::Cat(old, *id)));
            old = *count;
            *count += 1;
        }
    }
    old
}

fn transform(vec_ins: &[(Variable, Instruction)]) -> Result<Vec<(Variable, Element)>, failure::Error> {
    let mut res = Vec::new();
    let mut ins_to_elem = HashMap::new();
    let mut count = 0;
    for (var, ins) in vec_ins {
        match ins {
            Instruction::Input => {
                res.push((Variable { id: count, width: var.width },
                          Element::Input));
                ins_to_elem.insert(var.id, vec![count]);
                count += 1;
            },
            Instruction::Add(id_l, id_r) => {
                let ids_l = ins_to_elem.get(id_l).unwrap();
                let ids_r = ins_to_elem.get(id_r).unwrap();
                let ext_ids_l = ext_bits(ids_l, &mut res, &mut count);
                let ext_ids_r = ext_bits(ids_r, &mut res, &mut count);
                let mut old = count;
                res.push((Variable { id: count, width: 1 },
                          Element::Const(false)));
                count += 1;
                let mut elems = Vec::new();
                for (l, r) in ext_ids_l.iter().zip(ext_ids_r.iter()) {
                    res.push((Variable { id: count, width: 2 },
                              Element::FAdd(*l, *r, old)));
                    old = count;
                    count += 1;
                    res.push((Variable { id: count, width: 1 },
                              Element::Ext(old, 0, 1)));
                    elems.push(count);
                    count += 1;
                    res.push((Variable { id: count, width: 1 },
                              Element::Ext(old, 1, 2)));
                    old = count;
                    count += 1;
                }
                elems.push(old);
                ins_to_elem.insert(var.id, elems);
            },
            Instruction::Ext(id, first, last) => {
                let ids = ins_to_elem.get(id).unwrap();
                let cat_id = cat_bits(ids, &mut res, &mut count);
                res.push((Variable { id: count, width: last - first + 1},
                          Element::Ext(cat_id, *first, *last)));
                ins_to_elem.insert(var.id, vec![count]);
                count += 1;
            },
            Instruction::And(id_l, id_r) => {
                let ids_l = ins_to_elem.get(id_l).unwrap();
                let ids_r = ins_to_elem.get(id_r).unwrap();
                let ext_ids_l = ext_bits(ids_l, &mut res, &mut count);
                let ext_ids_r = ext_bits(ids_r, &mut res, &mut count);
                let fill_id = count;
                res.push((Variable { id: count, width: 1 },
                          Element::Const(false)));
                count += 1;
                let mut elems = Vec::new();
                for (l, r) in ext_ids_l.iter().zip(ext_ids_r.iter()) {
                    let inputs = [*l, *r, fill_id, fill_id, fill_id, fill_id];
                    res.push((Variable { id: count, width: 1 },
                              Element::LUT6(0x8888_8888_8888_8888u64, inputs)));
                    elems.push(count);
                    count += 1;
                }
                ins_to_elem.insert(var.id, elems);
            },
            Instruction::Const(bits) => {
                let mut elems = Vec::new();
                for idx in 0..var.width {
                    res.push((Variable { id: count, width: 1},
                              Element::Const(bits[idx])));
                    elems.push(count);
                    count += 1;
                }
                ins_to_elem.insert(var.id, elems);
            },
            Instruction::Cat(id_l, id_r) => {
                let mut ids_l = ins_to_elem.get(id_l).unwrap().clone();
                let ids_r = ins_to_elem.get(id_r).unwrap();
                ids_l.extend(ids_r);
                let cat_id = cat_bits(&ids_l, &mut res, &mut count);
                ins_to_elem.insert(var.id, vec![cat_id]);
            },
            _ => {
                unimplemented!();
            }
        }
    }
    let last_id = vec_ins.last().unwrap().0.id;
    let ids = ins_to_elem.get(&last_id).unwrap();
    let _ = cat_bits(ids, &mut res, &mut count);
    Ok(res)
}

use std::cmp::max;

fn cut(circuit: &Vec<(Variable, Element)>, constrains: &Vec<(usize, usize)>) -> Vec<(Variable, Element, usize)> {
    let mut graph = vec![Vec::new(); circuit.len()];
    for (from, to) in constrains {
        graph[*from].push((*to, 1));
    }
    let mut dist = vec![0; circuit.len()];
    for (var, elem) in circuit {
        match elem {
            Element::FAdd(a, b, c) => {
                dist[var.id] = max(dist[var.id], dist[*a]);
                dist[var.id] = max(dist[var.id], dist[*b]);
                dist[var.id] = max(dist[var.id], dist[*c]);
            },
            Element::LUT6(_, parents) => {
                for parent in parents {
                    dist[var.id] = max(dist[var.id], dist[*parent]);
                }
            },
            Element::Mul48(a, b) => {
                dist[var.id] = max(dist[var.id], dist[*a]);
                dist[var.id] = max(dist[var.id], dist[*b]);
            },
            Element::Ext(id, _, _) => {
                dist[var.id] = max(dist[var.id], dist[*id]);
            },
            Element::Cat(a, b) => {
                dist[var.id] = max(dist[var.id], dist[*a]);
                dist[var.id] = max(dist[var.id], dist[*b]);
            },
            _ => (),
        }
        for (to, cost) in &graph[var.id] {
            dist[*to] = max(dist[*to], dist[var.id] + cost);
        }
    }
    let mut result = Vec::new();
    for (var, elem) in circuit {
        result.push((var.clone(), elem.clone(), dist[var.id]));
    }
    result
}

mod verugent;
#[macro_use]
use verugent::vcore::*;

fn calc_regs(circuit: &Vec<(Variable, Element, usize)>)
    -> Vec<usize> {
    let mut reg_count = vec![0; circuit.len()];
    for (_, elem, lat) in circuit {
        match elem {
            Element::FAdd(a, b, c) => {
                reg_count[*a] = max(reg_count[*a], lat - circuit[*a].2);
                reg_count[*b] = max(reg_count[*b], lat - circuit[*b].2);
                reg_count[*c] = max(reg_count[*c], lat - circuit[*c].2);
            },
            Element::LUT6(_, parents) => {
                for parent in parents {
                    reg_count[*parent] = max(reg_count[*parent], lat - circuit[*parent].2);
                }
            }
            Element::Mul48(a, b) => {
                reg_count[*a] = max(reg_count[*a], lat - circuit[*a].2);
                reg_count[*b] = max(reg_count[*b], lat - circuit[*b].2);
            },
            Element::Ext(id, _, _) => {
                reg_count[*id] = max(reg_count[*id], lat - circuit[*id].2);
            },
            Element::Cat(a, b) => {
                reg_count[*a] = max(reg_count[*a], lat - circuit[*a].2);
                reg_count[*b] = max(reg_count[*b], lat - circuit[*b].2);
            },
            _ => (),
        }
    }
    reg_count
}

fn gen_lut6(m : &mut VModule, table: u64) -> Func_AST {
    let mut f = func(&format!("func_{}", table), 1);
    let mut inputs = Vec::new();
    for index in 0..6 {
        inputs.push(f.Input(&format!("in_{}", index), 1));
    }
    let mut prev = Vec::new();
    for index in 0..64 {
        let val = (table >> index) & 1;
        prev.push(_Num(val as i32));
    }
    let mut size = 32;
    for stage in 0..5 {
        let mut nexts = Vec::new();
        for index in 0..size {
            let res_0 = &prev[2*index];
            let res_1 = &prev[2*index+1];
            let input = &inputs[stage];
            nexts.push(_Branch(F!(input == 1), res_1, res_0));
        }
        prev = nexts;
        size /= 2;
    }
    let res_0 = &prev[0];
    let res_1 = &prev[1];
    let input = &inputs[5];
    f.If(F!(input == 1), Form(f.clone().own().sst(res_1)));
    f.Else(Form(f.clone().own().sst(res_0)));
    m.Function(f.clone());
    f
}

fn gen_verilog(circuit: &Vec<(Variable, Element, usize)>) -> String {
    let reg_count = calc_regs(circuit);
    let mut m = VModule::new("Circuit");
    let clk = m.Input("clk", 1);
    let rst = m.Input("rst", 1);

    let mut funcs = HashMap::<u64, Func_AST>::new();
    for (_, elem, _) in circuit {
        match elem {
            Element::LUT6(table, _) => {
                if !funcs.contains_key(table) {
                    funcs.insert(*table, gen_lut6(&mut m, *table));
                }
            },
            _ => ()
        }
    }
    let mut vals = HashMap::<(usize, usize), Box<E>>::new();
    for (var, elem, lat) in circuit {
        let width = var.width as i32;
        match elem {
            Element::Input => {
                vals.insert((var.id, 0),
                    m.Input(&format!("val_{}", var.id), width));
            },
            Element::FAdd(a, b, c) => {
                let lat_a = lat - circuit[*a].2;
                let val_a = vals.get(&(*a, lat_a)).unwrap();
                let lat_b = lat - circuit[*b].2;
                let val_b = vals.get(&(*b, lat_b)).unwrap();
                let lat_c = lat - circuit[*c].2;
                let val_c = vals.get(&(*c, lat_c)).unwrap();
                let val = m.Wire(&format!("val_{}", var.id), width);
                m.Assign(val._e(val_a + val_b + val_c));
                vals.insert((var.id, 0), val);
            },
            Element::LUT6(table, parents) => {
                let mut val6 = Vec::new();
                for parent in parents {
                    let lat_p = lat - circuit[*parent].2;
                    val6.push(vals.get(&(*parent, lat_p)).unwrap());
                }
                let f = funcs.get(table).unwrap();
                let val = m.Wire(&format!("val_{}", var.id), width);
                m.Assign(val._e(f.clone().using(
                            func_args!(val6[0], val6[1], val6[2],
                                       val6[3], val6[4], val6[5]))));
                vals.insert((var.id, 0), val);
            },
            Element::Mul48(a, b) => {
                let lat_a = lat - circuit[*a].2;
                let val_a = vals.get(&(*a, lat_a)).unwrap();
                let lat_b = lat - circuit[*b].2;
                let val_b = vals.get(&(*b, lat_b)).unwrap();
                let val = m.Wire(&format!("val_{}", var.id), width);
                m.Assign(val._e(val_a * val_b));
                vals.insert((var.id, 0), val);
            },
            Element::Ext(id, first, _) => {
                let lat_prev = lat - circuit[*id].2;
                let val_prev = vals.get(&(*id, lat_prev)).unwrap();
                let val = m.Wire(&format!("val_{}", var.id), width);
                m.Assign(val._e(val_prev >> _Num(*first as i32)));
                vals.insert((var.id, 0), val);
            },
            Element::Cat(a, b) => {
                let lat_a = lat - circuit[*a].2;
                let val_a = vals.get(&(*a, lat_a)).unwrap();
                let width_a = circuit[*a].0.width as i32;
                let lat_b = lat - circuit[*b].2;
                let val_b = vals.get(&(*b, lat_b)).unwrap();
                let val_temp = m.Wire(&format!("val_{}_shl", var.id), width);
                m.Assign(val_temp._e(val_b));
                let val = m.Wire(&format!("val_{}", var.id), width);
                m.Assign(val._e(val_a | (val_b << _Num(width_a))));
                vals.insert((var.id, 0), val);
            },
            Element::Const(bit) => {
                let val = m.Wire(&format!("val_{}", var.id), 1);
                m.Assign(val._e(_Num(*bit as i32)));
                vals.insert((var.id, 0), val);
            }
        }
        for count in 0..reg_count[var.id] {
            let prev = vals.get(&(var.id, count)).unwrap();
            let val = m.Reg(&format!("val_{}_reg_{}", var.id, count+1), width);
            m.Always(Posedge(&clk).Posedge(&rst).block()
                     .If(&rst, Form(F!(val = prev)))
                     .Else(Form(F!(val = prev))));
            vals.insert((var.id, count+1), val);
        }
    }

    let last = vals.get(&(circuit.len()-1, 0)).unwrap();
    let out = m.Output("out", circuit.last().unwrap().0.width as i32);
    m.Assign(out._e(last));
    m.endmodule()
}

#[derive(Debug, Fail)]
enum ParseConfigError {
    #[fail(display = "3 arguments required: source target frequency(MHz)")]
    NotEnoughArgumentError,
}

impl Config {
    pub fn new(args: &Vec<String>) -> Result<Config, failure::Error> {
        if args.len() < 4 {
            return Err(failure::Error::from(ParseConfigError::NotEnoughArgumentError));
        }
        let filename = &args[1];
        let target = &args[2];
        let frequency: usize = args[3].parse()?;
        Ok(Config { filename: filename.to_string(), target: target.to_string(), frequency })
    }
}

use std::env;
use std::process;

fn main() {
    let args: Vec<String> = env::args().collect();
    let config = Config::new(&args).unwrap_or_else(|err| {
        println!("{}", err);
        process::exit(1);
    });
    let vec_ins = parse(&config.filename).unwrap_or_else(|err| {
        println!("Parse Error: {:?}", err);
        process::exit(1);
    });
    let vec_elem = transform(&vec_ins).unwrap_or_else(|err| {
        println!("Transform Error: {:?}", err);
        process::exit(1);
    });
    let constraints = Vec::new();
    let phases = cut(&vec_elem, &constraints);
    let code = gen_verilog(&phases);
    let mut file = File::create("circuit.v").unwrap();
    write!(file, "{}", code).unwrap();
    file.flush().unwrap();
}
