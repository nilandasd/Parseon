#![allow(dead_code)]

use std::collections::HashSet;

type StateID = usize;
type TokenID = usize;
type ProdID = usize;

struct Token {
    id: TokenID,
    string: String,
}

struct ParsingError {

}

#[derive(Clone)]
enum Action {
    Accept,
    Error,
    Reduce(usize, ProdID),
    Shift(StateID),
    Goto(StateID),
}

#[derive(PartialEq, Eq, Hash, Clone, Copy)]
enum Symbol {
    Start,
    Accept,
    DNE,
    Epsilon,
    Cursor,
    Token(TokenID),
}

#[derive(Clone)]
struct Prod {
    head: Symbol,
    body: Vec<Symbol>,
}

#[derive(Clone)]
struct State {
    items: Vec<Item>,
    gotos: Vec<(Symbol, usize)>,
}

#[derive(Clone)] // partialEq
struct Item {
    head: Symbol,
    body: Vec<Symbol>,
    la: Vec<Symbol>,
}

pub struct Bovidae {
    prods: Vec<Prod>,
    states: Vec<State>,
    prop_table: Vec<((StateID, usize), (StateID, usize))>,
    epsilon_symbols: Vec<Symbol>,
    action_table: Vec<Vec<Action>>,
    state_stack: Vec<StateID>,
    tokens: Vec<Token>,
}

impl Prod {
    pub fn to_item(&self) -> Item {
        let mut new_body = Vec::<Symbol>::new();

        new_body.push(Symbol::Cursor);

        for sym in self.body.iter() {
            if *sym == Symbol::Epsilon { continue; }
            new_body.push(*sym);
        }

        Item {
            head: self.head,
            body: new_body,
            la: vec![],
        }
    }
}

impl PartialEq for State {
    fn eq(&self, other: &Self) -> bool {
        self.items == other.items
    }
}

impl PartialEq for Item {
    fn eq(&self, other: &Self) -> bool {
        self.head == other.head && self.body == other.body
    }
}

impl State {
    pub fn possible_moves(&self) -> Vec<Symbol> {
        let mut possible_moves = vec![];

        for item in self.items.iter() {
            let expected_symbol = item.expects();

            if expected_symbol.is_some() && !possible_moves.contains(&expected_symbol.unwrap()) {
                possible_moves.push(expected_symbol.unwrap());
            }
        }

        possible_moves
    }
     
    pub fn remove_nonkernel_items(&mut self) {
        self.items = self.items.iter().filter(|i| i.is_kernel()).cloned().collect();
    }
}

impl Item {
    pub fn expects(&self) -> Option<Symbol> {
        let mut cursor_flag = false;

        for sym in self.body.iter() {
            if cursor_flag {
                return Some(*sym);
            } else if *sym == Symbol::Cursor {
                cursor_flag = true;
            }
        }

        return None;
    }

    pub fn shift_cursor(&self) -> Self {
        let mut new_body = Vec::<Symbol>::new();
        let mut cursor_flag = false;

        for sym in self.body.iter() {
            if *sym == Symbol::Cursor {
                cursor_flag = true;
            } else if cursor_flag {
                new_body.push(*sym);
                new_body.push(Symbol::Cursor);
                cursor_flag = false;
            } else {
                new_body.push(*sym);
            }
        }

        Item {
            head: self.head,
            body: new_body,
            la: vec![],
        }
    }

    pub fn is_kernel(&self) -> bool {
        self.body[0] != Symbol::Cursor || self.head == Symbol::Start
    }

    pub fn postfix(&self, s: Symbol) -> Vec<Symbol> {
        let mut result = Vec::<Symbol>::new();
        let mut cursor_flag = false;
        let mut push_flag = false;

        for sym in self.body.iter() {
            if push_flag {
                result.push(*sym);
            } else if *sym == Symbol::Cursor {
                cursor_flag = true;
            } else if cursor_flag {
                push_flag = true;
            }
        }

        result.push(s);

        result
    }
}

impl Bovidae {
    pub fn new() -> Self {
        Self {
            prods: Vec::<Prod>::new(),
            states: Vec::<State>::new(),
            prop_table: Vec::<((StateID, usize), (StateID, usize))>::new(),
            epsilon_symbols: Vec::<Symbol>::new(),
            action_table: Vec::<Vec<Action>>::new(),
            state_stack: Vec::<StateID>::new(),
            tokens: Vec::<Token>::new(),
        }
    }

    pub fn set_prods(&mut self, prods: &Vec<(&str, &Vec<&str>)>) {
        for prod in prods {
            self.set_prod(prod.0, prod.1);
        }
    }

    pub fn set_prod(&mut self, head_str: &str, body_strs: &Vec<&str>) {
        let head = Symbol::Token(self.get_token_id(head_str));
        let mut body = Vec::<Symbol>::new();

        for b in body_strs.iter() {
           body.push(Symbol::Token(self.get_token_id(b))) ;
        }

        if body_strs.is_empty() {
            body.push(Symbol::Epsilon);
        }

        self.prods.push(Prod { head, body });
    }

    pub fn set_token(&mut self, string: &str) -> TokenID {
        for tok in self.tokens.iter() {
            if tok.string == string {
                panic!("Token '{}' was defined twice.", string);
            }
        }

        let id = self.tokens.len();

        self.tokens.push(
            Token {
                id,
                string: string.to_string()
            });

        id
    }

    pub fn get_token_id(&mut self, tok_str: &str) -> TokenID {
        for tok in self.tokens.iter() {
            if tok.string == *tok_str {
                return tok.id;
            }
        }

        self.set_token(tok_str)
    }

    pub fn parse(&mut self, tokens: &Vec<TokenID>) -> Result<(), ()> {
        self.state_stack.push(0);

        let mut token_idx = 0;
        let mut reduction_token = 0;
        let mut reduction_flag = false;

        while token_idx <= tokens.len() {
            let current_state = *self.state_stack.last().unwrap();
            let action: &Action;
            if token_idx == tokens.len() {
                action = &Action::Accept;
            } else if reduction_flag {
                reduction_flag = false;
                action = &self.action_table[current_state][reduction_token];
            } else {
                let token = tokens[token_idx];
                action = &self.action_table[current_state][token];
            }

            match action {
                Action::Accept => return Ok(()),
                Action::Error => return Err(()),
                Action::Goto(sid) => self.state_stack.push(*sid),
                Action::Shift(sid) => {
                    token_idx += 1;
                    self.state_stack.push(*sid);
                }
                Action::Reduce(pop_count, tid) => {
                    for _ in 0..*pop_count {
                        self.state_stack.pop();
                    }
                    reduction_token = *tid;
                    reduction_flag = true;
                }
            }
        }

        return Err(())
    }

    // 1. build LR(0) items
    // 2. create propagation table
    // 3. propagate lookaheads
    // 4. construct parsing table
    pub fn generate_parser(&mut self) {
        self.find_epsilon_symbols();
        self.create_states();
        self.build_prop_table();
        self.prop_lookaheads();
        self.la_close_kernels();
        self.create_action_table();
        self.clean();
    }

    fn clean(&mut self) {
        self.epsilon_symbols.clear();
        self.prop_table.clear();
        self.states.clear()
    }

    fn add_shift_and_goto_actions(&self, action_table_row: &mut Vec<Action>, state: &State) {
        for goto in state.gotos.iter() {
            let goto_state_id = goto.1;
            if let Symbol::Token(tid) = goto.0 {
                if self.get_prods(goto.0).is_empty() {
                    action_table_row[tid] = Action::Shift(goto_state_id);
                } else {
                    action_table_row[tid] = Action::Goto(goto_state_id);
                }
            }
        }
    }

    fn add_reductions(&self, action_table_row: &mut Vec<Action>, state: &State) {
        let mut reductions = Vec::<(usize, usize, Action)>::new();

        for item in state.items.iter() {
            if item.expects().is_some() || item.head == Symbol::Start { continue; }

            for la in item.la.iter() {
                let mut reduction_tid: TokenID = 0; // the tokenID that we reduce to ie A -> a means the reduction tid is A
                if let Symbol::Token(item_head_tid) = item.head {
                    reduction_tid = item_head_tid;
                }

                let action_tid: TokenID; // the symbol that we must see in the input to perform the reduction
                if let Symbol::Token(la_tid) = la {
                    action_tid = *la_tid;
                } else {
                    action_tid = self.tokens.len();
                }

                if let Action::Shift(_) = action_table_row[action_tid] {
                    continue; // avoid shift / reduce conflicts
                }

                let this_prod_id = self.get_prod_id(&item);

                let mut replace_idx = -1;
                let mut add_flag = true;
                for (idx, reduction) in reductions.iter().enumerate() {
                    let other_prod_id = reduction.0;
                    let action_tid = reduction.1;

                    if Symbol::Token(action_tid) == *la || (Symbol::Accept == *la && action_tid == self.tokens.len()) {
                        if this_prod_id < other_prod_id {
                            replace_idx = idx as i16;
                        } else {
                            add_flag = false;
                        }
                        break;
                    }
                }

                // this is to resolve reduce / reduce conflicts
                let reduction_action = (this_prod_id, action_tid, Action::Reduce(item.body.len() - 1, reduction_tid));

                if replace_idx != -1 {
                    reductions[replace_idx as usize] = reduction_action;
                } else if add_flag {
                    reductions.push(reduction_action);
                }
            }
        }

        for reduction in reductions.iter() {
            action_table_row[reduction.1] = reduction.2.clone();
        }
    }

    fn create_action_table(&mut self) {
        for (state_id, state) in self.states.iter().enumerate() {
            let mut action_table_row = vec![Action::Error; self.tokens.len() + 1]; // + 1 for accept symbol

            self.add_shift_and_goto_actions(&mut action_table_row, state);
            self.add_reductions(&mut action_table_row, state);

            // state 1 is always the accept state
            if state_id == 1 {
                action_table_row[self.tokens.len()] = Action::Accept;
            }

            self.action_table.push(action_table_row);
        }
    }

    pub fn print_action_table(&self) {
        println!("\t\t----- ACTION TABLE -----");

        for tok in self.tokens.iter() {
            print!("\t{} ", tok.string);
        }

        print!("\tACCEPT");
        println!("");

        for (idx, row) in self.action_table.iter().enumerate() {
            print!("{} | ", idx);

            for action in row.iter() {
                match action {
                    Action::Reduce(n, _) => print!("\tR{}", n),
                    Action::Goto(id) => print!("\tG{}", id),
                    Action::Shift(id) => print!("\tS{}", id),
                    Action::Accept => print!("\tAcc"),
                    Action::Error => print!("\t"),
                }

            }

            println!("");
        }

        println!("");
    }

    fn get_prod_id(&self, item: &Item) -> ProdID {
        let item_body: Vec<Symbol> = item.body.clone().iter().filter(|s| **s != Symbol::Cursor).cloned().collect();

        for (idx, prod) in self.prods.iter().enumerate() {
            if prod.body[0] == Symbol::Epsilon && item_body.len() == 0 && prod.head == item.head {
                return idx;
            } else if prod.head == item.head && prod.body == item_body {
                return idx;
            }
        }

        panic!("PARSING ERROR: UNABLE TO FIND PRODUCTION")
    }

    fn la_close_kernels(&mut self) {
        for i in 0..self.states.len() {
            self.states[i].remove_nonkernel_items();

            let closure = self.la_closure(&self.states[i].items);

            for item in closure {
                if item.is_kernel() { continue; }

                self.states[i].items.push(item);
            }
        }
    }

    fn prop_lookaheads(&mut self) {
        let mut addition_flag = true;

        while addition_flag {
            addition_flag = false;

            for prop in self.prop_table.iter() {
                let src_coords = prop.0;
                let target_coords = prop.1;

                for la in self.states[src_coords.0].items[src_coords.1].la.clone().iter() {
                    if self.states[target_coords.0].items[target_coords.1].la.contains(&la) { continue; }

                    addition_flag = true;
                    self.states[target_coords.0].items[target_coords.1].la.push(*la);
                }
            }
        }
    }

    fn build_prop_table(&mut self) {
        for row in 0..self.states.len() {
            for col in 0..self.states[row].items.len() {
                if !self.states[row].items[col].is_kernel() { continue; }

                let mut modified_kernel_item = self.states[row].items[col].clone();
                modified_kernel_item.la = vec![Symbol::DNE];

                let la_items = self.la_closure(&vec![modified_kernel_item]);

                for la_item in la_items.iter() {
                    if la_item.expects().is_none() { continue; }

                    let target_item_coord = self.get_prop_item_coord(row, &la_item);

                    for la in la_item.la.iter() {
                        if *la == Symbol::DNE {
                            self.prop_table.push(((row, col), target_item_coord)); // create a propagation entry from this item to the target item
                        } else if !self.states[target_item_coord.0].items[target_item_coord.1].la.contains(&la) {
                            self.states[target_item_coord.0].items[target_item_coord.1].la.push(*la); // spontaneously generate the lookahead
                        }
                    }
                }
            }
        }
    }

    fn la_closure(&self, items_to_close: &Vec<Item>) -> Vec<Item> {
        let mut closure_items = items_to_close.clone();
        let mut checked_items = 0;

        while checked_items != closure_items.len() {
            for i in checked_items..closure_items.len() {
                let expected_symbol = closure_items[i].expects();
                checked_items += 1;

                if expected_symbol.is_none() { continue; }

                for la in closure_items[i].la.clone().iter() {
                    let lookaheads: Vec<Symbol> = self.first(&closure_items[i].postfix(*la), &vec![]).iter()
                    .filter(|s| **s != Symbol::Epsilon).cloned().collect();

                    for prod in self.get_prods(expected_symbol.unwrap()).iter() {
                        let mut new_item = prod.to_item();
                        new_item.la = lookaheads.clone();

                        let mut contains_flag = false;
                        for item in closure_items.iter_mut() {
                            if *item == new_item {
                                contains_flag = true;
                                for la in new_item.la.iter() {
                                    if !item.la.contains(&la) {
                                        item.la.push(*la);
                                    }
                                }
                                break;
                            }
                        }

                        if !contains_flag {
                            closure_items.push(new_item);
                        }
                    }
                }
            }
        }

        closure_items
    }

    fn find_epsilon_symbols(&mut self) {
        let mut addition_flag = true;

        while addition_flag {
            addition_flag = false;

            for prod in self.prods.iter() {
                if self.epsilon_symbols.contains(&prod.head) {
                    continue;
                }

                if prod.body[0] == Symbol::Epsilon {
                    addition_flag = true;
                    self.epsilon_symbols.push(prod.head);
                    continue;
                }

                let mut epsilon_flag = true;
                for sym in prod.body.iter() {
                    if !self.epsilon_symbols.contains(sym) { 
                        epsilon_flag = false;
                        break;
                    }
                }

                if epsilon_flag {
                    addition_flag = true;
                    self.epsilon_symbols.push(prod.head);
                }
            }
        }
    }

    fn first(&self, symbols: &Vec<Symbol>, currently_calculating: &Vec<Symbol>) -> Vec<Symbol> {
        let mut result = HashSet::<Symbol>::new();

        for symbol in symbols.iter() {
            if currently_calculating.contains(&symbol) {
                if self.epsilon_symbols.contains(&symbol) {
                    continue;
                } else {
                    break;
                }
            }

            let prods = self.get_prods(*symbol);
            if prods.is_empty() {
                result.insert(*symbol);
                break;
            }

            let mut new_currently_calculating = currently_calculating.clone();
            new_currently_calculating.push(*symbol);

            let mut epsilon_flag = false;
            for prod in prods.iter() {
                let other_result = self.first(&prod.body, &new_currently_calculating);

                for s in other_result {
                    if s == Symbol::Epsilon {
                        epsilon_flag = true;
                    }
                    result.insert(s);
                }
            }

            if !epsilon_flag {
                break;
            }
        }

        result.into_iter().collect()
    }

    fn get_prop_item_coord(&self, state_row: usize, item: &Item) -> (usize, usize) {
        let target_item = item.shift_cursor();
        let mut target_state = 0;
        for goto in self.states[state_row].gotos.iter() {
            if goto.0 == item.expects().unwrap() {
                target_state = goto.1;
                break;
            }
        }

        for col in 0..self.states[target_state].items.len() {
            if target_item == self.states[target_state].items[col] {
                return (target_state, col);
            }
        }

        panic!("unreachable");
    }

    fn create_start_state(&mut self) {
        let augmented_start_item = Item {
            head: Symbol::Start,
            body: vec![Symbol::Cursor, self.prods[0].head],
            la: vec![Symbol::Accept],
        };

        let start_state = State {
            items: self.canonical_closure(&vec![augmented_start_item]),
            gotos: vec![],
        };

        self.states.push(start_state);
    }

    fn create_states(&mut self) {
        let mut checked_count = 0;

        self.create_start_state();

        while checked_count != self.states.len() {
            for i in checked_count..self.states.len() {
                checked_count += 1;

                for sym in self.states[i].possible_moves().iter() {
                    let new_state_kernel = self.canonical_goto(&self.states[i].items.clone(), *sym);
                    let new_state_items = self.canonical_closure(&new_state_kernel);
                    let new_state = State {
                        items: new_state_items,
                        gotos: vec![],
                    };

                    let existing_state = self.states.iter().position(|state| *state == new_state);
                    match existing_state {
                        Some(existing_state_id) => {
                            self.states[i].gotos.push((*sym, existing_state_id));
                        }
                        None => {
                            let new_state_id = self.states.len();

                            self.states[i].gotos.push((*sym, new_state_id));
                            self.states.push(new_state);
                        }
                    }
                }
            }
        }
    }

    fn canonical_closure(&self, init_items: &Vec<Item>) -> Vec<Item> {
        let mut closure_items = init_items.clone();
        let mut checked_prod_symbols = Vec::<Symbol>::new();
        let mut checked_count = 0;

        while checked_count != closure_items.len() {
            for i in checked_count..closure_items.len() {
                let expected_symbol = closure_items[i].expects();
                checked_count += 1;

                if expected_symbol.is_none() { continue; }
                if checked_prod_symbols.contains(&expected_symbol.unwrap()) { continue; }

                checked_prod_symbols.push(expected_symbol.unwrap());

                for prod in self.get_prods(expected_symbol.unwrap()).iter() {
                    let new_item = prod.to_item();

                    if !closure_items.contains(&new_item) {
                        closure_items.push(new_item);
                    }
                }
            }
        }

        closure_items
    }

    fn canonical_goto(&self, init_items: &Vec<Item>, move_sym: Symbol) -> Vec<Item> {
        let mut result = Vec::<Item>::new();

        for item in init_items.iter() {
            match item.expects() {
                Some(sym) => {
                    if sym == move_sym {
                        result.push(item.shift_cursor());
                    }
                }
                None => {}
            }
        }

        result
    }

    fn get_prods(&self, head: Symbol) -> Vec<Prod> {
        let mut result = Vec::<Prod>::new();

        for prod in self.prods.iter() {
            if prod.head == head {
                result.push(prod.clone());
            }
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let mut bovidae = Bovidae::new();
        bovidae.set_prods(&vec![
            ("E", &vec!["E", "+", "T"]),
            ("E", &vec!["T"]          ),
            ("T", &vec!["T", "*", "F"]),
            ("T", &vec!["F"]          ),
            ("F", &vec!["(", "E", ")"]),
            ("F", &vec!["id"]         ),
        ]);
        bovidae.generate_parser();
        //bovidae.print_action_table();

        let id = bovidae.get_token_id("id");
        let plus = bovidae.get_token_id("+");
        let left_paren = bovidae.get_token_id("(");
        let right_paren = bovidae.get_token_id(")");

        let mut tokens = vec![id, plus, left_paren, id, right_paren];

        assert!(bovidae.parse(&mut tokens).is_ok());
    }

    #[test]
    fn it_works2() {
        let mut bovidae = Bovidae::new();
        bovidae.set_prods(&vec![
            ("S", &vec!["C", "C"]),
            ("C", &vec!["c", "C"]),
            ("C", &vec!["d"]),
        ]);
        bovidae.generate_parser();
        //bovidae.print_action_table();
        let c = bovidae.get_token_id("c");
        let d = bovidae.get_token_id("d");

        let mut tokens = vec![c, c, c, c, c, d, c, d];

        assert!(bovidae.parse(&mut tokens).is_ok());

        let mut tokens = vec![c, d, c, d, c];

        assert!(bovidae.parse(&mut tokens).is_err());
    }

    #[test]
    fn it_works3() {
        let mut bovidae = Bovidae::new();
        bovidae.set_prods(&vec![
            ("S", &vec!["L", "=", "R"]),
            ("S", &vec!["R"]),
            ("L", &vec!["*", "R"]),
            ("L", &vec!["id"]),
            ("R", &vec!["L"]),
        ]);
        bovidae.generate_parser();
        //bovidae.print_action_table();

        let eq = bovidae.get_token_id("=");
        let times = bovidae.get_token_id("*");
        let id = bovidae.get_token_id("id");

        let mut tokens = vec![times, id, eq, times, id];

        assert!(bovidae.parse(&mut tokens).is_ok());

        let mut tokens = vec![times, id, eq, times, id, id];

        assert!(bovidae.parse(&mut tokens).is_err());
    }

    #[test]
    fn it_works4() {
        let mut bovidae = Bovidae::new();
        bovidae.set_prods(&vec![
            ("S", &vec!["s"]),
            ("S", &vec!["i", "S", "t", "S"]),
            ("S", &vec!["i", "S", "t", "S", "e", "S"]),
        ]);
        bovidae.generate_parser();
        //bovidae.print_action_table();

        let i = bovidae.get_token_id("i");
        let t = bovidae.get_token_id("t");
        let e = bovidae.get_token_id("e");
        let s = bovidae.get_token_id("s");

        let mut tokens = vec![i, s, t, s, e, s];

        assert!(bovidae.parse(&mut tokens).is_ok());

        let mut tokens = vec![i, s, t, s, i, s];

        assert!(bovidae.parse(&mut tokens).is_err());
    }

    #[test]
    fn it_works5() {
        let mut bovidae = Bovidae::new();
        bovidae.set_prods(&vec![
            ("S", &vec!["A", "B"]),
            ("A", &vec!["a", "A"]),
            ("A", &vec![]),
            ("B", &vec!["b", "B"]),
            ("B", &vec![]),
        ]);
        bovidae.generate_parser();
        //bovidae.print_action_table();

        let a = bovidae.get_token_id("a");
        let b = bovidae.get_token_id("b");

        let accept_strings: Vec<Vec<TokenID>> = vec![
            vec![a, a, b, b],
            vec![a, b],
            vec![a, a],
            vec![b, b],
            vec![],
        ];

        let reject_strings: Vec<Vec<TokenID>> = vec![
            vec![b, a],
            vec![a, b, a],
            vec![a, b, a, b],
        ];

        for s in accept_strings {
            assert!(bovidae.parse(&s).is_ok());
        }

        for s in reject_strings {
            assert!(bovidae.parse(&s).is_err());
        }
    }
}