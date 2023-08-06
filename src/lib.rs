use std::collections::HashSet;

// ========== PUBLIC TYPES ==========

// ProdID's are set incrementally with the first prod set having a ProdID of 0.
// the second prod having id 1, etc... ProdID's are exposed publiclly so when a
// reduction happens the ProdID of the reduced production can be returned to
// the user of the parser.
pub type ProdID = usize;

// Err() type returned by the parse method
#[derive(Debug)]
pub enum ParseonError {
    PassedNonTerm,
    // the token passed was not defined in the grammar
    BadToken,
}

// the Parseon struct takes 2 generic type parameters of Token and Node
// A token is usually a enum type or usize which represent which act as
// identifiers for every terminal and non-terminal in the defined languages grammar.
//
// A node has no generic contraits, but is meant to be a struct of some kindw, 
// which can be used to build the ast
pub struct Parseon<Token, Node>
where Token: Copy + Clone + PartialEq + std::fmt::Debug
{
    action_table: Vec<Vec<Action>>,// TODO: compile the action table into rust code!
    epsilon_symbols: Vec<Symbol>,
    prods: Vec<(Prod, Option<fn(&mut Vec<Node>)>)>,
    prop_table: Vec<((StateID, usize), (StateID, usize))>,
    states: Vec<State>,
    state_stack: Vec<StateID>,
    token_ids: Vec<(Token, Option<fn(&mut Vec<Node>)>)>,
    node_stack: Vec<Node>,
}

// ========== PUBLIC METHODS =========

impl<Token, Node> Parseon<Token, Node>
where Token: Copy + Clone + std::fmt::Debug + PartialEq
{
    pub fn new() -> Self {
        Self {
            action_table: Vec::<Vec<Action>>::new(),
            epsilon_symbols: Vec::<Symbol>::new(),
            prods: Vec::<(Prod, Option<fn(&mut Vec<Node>)>)>::new(),
            prop_table: Vec::<((StateID, usize), (StateID, usize))>::new(),
            states: Vec::<State>::new(),
            state_stack: Vec::<StateID>::from([0]),
            token_ids: Vec::<(Token, Option<fn(&mut Vec<Node>)>)>::new(),
            node_stack: Vec::<Node>::new(),
        }
    }

    pub fn set_prods(&mut self, prods: &Vec<(Token, &Vec<Token>, Option<fn(&mut Vec<Node>)>)>) {
        for prod in prods {
            self.set_prod(prod.0, prod.1, prod.2);
        }
    }

    pub fn set_prod(&mut self, head: Token, body: &Vec<Token>, hook: Option<fn(&mut Vec<Node>)>) {
        let head_tid = self.get_or_create_token_id(head);
        let head_sym = Symbol::Token(head_tid);
        let mut body_sym = Vec::<Symbol>::new();

        for tid in body.iter() {
            body_sym.push(Symbol::Token(self.get_or_create_token_id(*tid)));
        }

        if body.is_empty() {
            body_sym.push(Symbol::Epsilon);
        }

        self.prods.push((Prod { head: head_sym, body: body_sym }, hook));
    }

    pub fn shift_hook(&mut self, token: Token, hook: fn(&mut Vec<Node>)) {
        let tid = self.get_token_id(token);

        self.token_ids[tid] = (token, Some(hook));
    }

    pub fn reset(&mut self) {
        self.state_stack = Vec::<StateID>::from([0]);
        self.node_stack.clear();
    }

    pub fn parse_tokens(&mut self, tokens: Vec<Token>) -> Result<(), ParseonError> {
        self.reset();

        for token in tokens {
            self.parse(token)?;
        }

        self.accept()?;

        Ok(())
    }

    pub fn accept(&mut self) -> Result<Option<Node>, ParseonError> {
        let accept_tid = self.action_table[0].len() - 1;

        loop {
            let current_state = *self.state_stack.last().unwrap();
            let action = self.action_table[current_state][accept_tid];

            self.take_action(action)?;

            if let Action::Accept = action {
                break;
            }
        }


        Ok(self.node_stack.pop())
    }

    // This function performs actions on the action table with the given token
    // until a shift action is reached. If any reductions occur during this 
    // process, the respective reduction hooks will be called. Also when the
    // token is shifted its shift hook will be called.
    pub fn parse(&mut self, token: Token) -> Result<(), ParseonError> {
        let tid = self.get_token_id(token);

        loop {
            let current_state = *self.state_stack.last().unwrap();
            let action = self.action_table[current_state][tid];

            self.take_action(action)?;

            if let Action::Shift(..) = action {
                if let Some(hook) = self.token_ids[tid].1 {
                    hook(&mut self.node_stack);
                }

                break;
            }
        }

        Ok(())
    }

    // Meant to be called after inserting all productions.
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
        // TODO: self.minimize action_table equivalent rows on the action table can be combined
        self.clean();
    }

    // prints the action table created after calling generate_parser
    // TODO: printed action table can be broken if token names are too long
    pub fn print_action_table(&self) {
        println!("\t\t----- ACTION TABLE -----");

        for tok in self.token_ids.iter() {
            print!("\t{:?} ", tok.0);
        }

        print!("\tACCEPT");
        println!("");

        for (idx, row) in self.action_table.iter().enumerate() {
            print!("{} | ", idx);

            for action in row.iter() {
                match action {
                    Action::Reduce(n, _, _) => print!("\tR{}", n),
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
}

// ========== PRIVATE TYPES ==========

type TokenID = usize;
type StateID = usize;

#[derive(Clone, Copy)]
enum Action {
    Accept,
    Error,
    Reduce(usize, TokenID, ProdID),
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

#[derive(Clone)]
struct Item {
    head: Symbol,
    body: Vec<Symbol>,
    la: Vec<Symbol>,
}

impl Prod {
    fn to_item(&self) -> Item {
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
    fn possible_moves(&self) -> Vec<Symbol> {
        let mut possible_moves = vec![];

        for item in self.items.iter() {
            let expected_symbol = item.expects();

            if expected_symbol.is_some() && !possible_moves.contains(&expected_symbol.unwrap()) {
                possible_moves.push(expected_symbol.unwrap());
            }
        }

        possible_moves
    }
     
    fn remove_nonkernel_items(&mut self) {
        self.items = self.items.iter().filter(|i| i.is_kernel()).cloned().collect();
    }
}

impl Item {
    fn expects(&self) -> Option<Symbol> {
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

    fn shift_cursor(&self) -> Self {
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

    fn is_kernel(&self) -> bool {
        self.body[0] != Symbol::Cursor || self.head == Symbol::Start
    }

    fn postfix(&self, s: Symbol) -> Vec<Symbol> {
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

impl<Token, Node> Parseon<Token, Node>
where Token: Copy + Clone + std::fmt::Debug + PartialEq
{
    fn take_action(&mut self, action: Action) -> Result<(), ParseonError> {
        match action {
            Action::Accept => Ok(()), 
            Action::Error => Err(ParseonError::BadToken),
            Action::Goto(_) => Err(ParseonError::BadToken),
            Action::Shift(sid) => {
                self.state_stack.push(sid);
                Ok(())
            }
            Action::Reduce(body_size, tid, pid) => {
                for _ in 0..body_size {
                    self.state_stack.pop();
                }

                if let (_, Some(hook)) = &self.prods[pid] {
                    hook(&mut self.node_stack);
                }

                let new_state = *self.state_stack.last().unwrap();
                let goto_action = &self.action_table[new_state][tid];

                if let Action::Goto(state_id) = goto_action {
                    self.state_stack.push(*state_id);
                    Ok(())
                } else {
                    // return Err(ParseonError::BadGrammar)
                    unreachable!("hmm this might not be unreachable bad grammar is defined?")
                }
            }
        }
    }

    fn get_or_create_token_id(&mut self, id: Token) -> TokenID {
        match self.token_ids.iter().position(|x| x.0 == id) {
            Some(idx) => idx,
            None => {
                self.token_ids.push((id, None));
                return self.token_ids.len() - 1;
            }
        }
    }

    fn get_token_id(&self, id: Token) -> TokenID {
        match self.token_ids.iter().position(|x| x.0 == id) {
            Some(idx) => idx,
            None => { panic!("parser error"); }
        }
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
                if self.is_terminal(goto.0) {
                    action_table_row[tid] = Action::Shift(goto_state_id);
                } else {
                    action_table_row[tid] = Action::Goto(goto_state_id);
                }
            }
        }
    }

    fn add_reductions(&self, action_table_row: &mut Vec<Action>, state: &State) {
        for item in state.items.iter() {
            if item.expects().is_some() || item.head == Symbol::Start { continue; }

            for la in item.la.iter() {
                let action_tid: TokenID; // the symbol that we must see in the input to perform the reduction
                if let Symbol::Token(la_tid) = la {
                    action_tid = *la_tid;
                } else {
                    action_tid = self.token_ids.len();
                }

                let mut reduction_tid: TokenID = 0; // the tokenID that we reduce to ie A -> a means the reduction tid is A
                if let Symbol::Token(item_head_tid) = item.head {
                    reduction_tid = item_head_tid;
                }
                let this_prod_id = self.get_prod_id(&item);
                let reduction_action = Action::Reduce(item.body.len() - 1, reduction_tid, this_prod_id);

                match action_table_row[action_tid] {
                    Action::Reduce(_, _, other_pid) => {
                        if this_prod_id < other_pid {
                            action_table_row[action_tid] = reduction_action;
                        }
                    }
                    Action::Error => {
                        action_table_row[action_tid] = reduction_action;
                    }
                    _ => continue,
                } 
            }
        }
    }

    fn create_action_table(&mut self) {
        for (state_id, state) in self.states.iter().enumerate() {
            let mut action_table_row = vec![Action::Error; self.token_ids.len() + 1]; // + 1 for accept symbol

            self.add_shift_and_goto_actions(&mut action_table_row, state);
            self.add_reductions(&mut action_table_row, state);

            // state 1 is always the accept state
            if state_id == 1 {
                action_table_row[self.token_ids.len()] = Action::Accept;
            }

            self.action_table.push(action_table_row);
        }
    }

    fn get_prod_id(&self, item: &Item) -> ProdID {
        let item_body: Vec<Symbol> = item.body.iter().filter(|s| **s != Symbol::Cursor).cloned().collect();

        for (idx, (prod, _)) in self.prods.iter().enumerate() {
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

                for i in 0..self.states[src_coords.0].items[src_coords.1].la.len() {
                    let la = self.states[src_coords.0].items[src_coords.1].la[i];
                    if self.states[target_coords.0].items[target_coords.1].la.contains(&la) { continue; }

                    addition_flag = true;
                    self.states[target_coords.0].items[target_coords.1].la.push(la);
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

                for k in 0..closure_items[i].la.len() {
                    let la = closure_items[i].la[k];
                    let lookaheads: Vec<Symbol> = self.first(&closure_items[i].postfix(la), &vec![])
                        .into_iter()
                        .filter(|s| *s != Symbol::Epsilon)
                        .collect();

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

            for (prod, _) in self.prods.iter() {
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
            body: vec![Symbol::Cursor, self.prods[0].0.head],
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
                    let new_state_kernel = self.canonical_goto(&self.states[i].items, *sym);
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

    fn get_prods(&self, head: Symbol) -> Vec<&Prod> {
        let mut result = Vec::<&Prod>::new();

        for (prod, _) in self.prods.iter() {
            if prod.head == head {
                result.push(prod);
            }
        }

        result
    }

    fn is_terminal(&self, head: Symbol) -> bool {
        for (prod, _) in self.prods.iter() {
            if prod.head == head { return false; }
        }

        return true;
    }
}

// ======================================================
// ========== TESTS =====================================
// ======================================================


#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Copy, Clone, Debug, PartialEq)]
    enum Tok {
        A, B, C, D, E, F, T, Plus, Times, Id, Lparen, Rparen, S, P, L, R, First, Second, Last, End, X, Expr, Num, Stmts, Stmt, Let, Semi, Eq
    }

    #[test]
    fn simple_grammar1() {
        let mut parser = Parseon::<Tok, ()>::new();

        parser.set_prods(&vec![
            (Tok::E, &vec![Tok::T], None),
            (Tok::T, &vec![Tok::T, Tok::Plus, Tok::F], None),
            (Tok::T, &vec![Tok::T, Tok::Times, Tok::F], None),
            (Tok::T, &vec![Tok::F], None),
            (Tok::F, &vec![Tok::Lparen, Tok::E, Tok::Rparen], None),
            (Tok::F, &vec![Tok::Id], None),
        ]);

        parser.generate_parser();
        // parser.print_action_table();

        let accept_strings: Vec<Vec<Tok>> = vec![
            vec![Tok::Id, Tok::Times, Tok::Lparen, Tok::Id, Tok::Plus, Tok::Id, Tok::Rparen],
            vec![Tok::Id, Tok::Times, Tok::Lparen, Tok::Id, Tok::Rparen],
            vec![Tok::Lparen, Tok::Id, Tok::Plus, Tok::Id, Tok::Rparen],
            vec![Tok::Id, Tok::Times, Tok::Id, Tok::Plus, Tok::Id],
            vec![Tok::Id, Tok::Times, Tok::Id],
            vec![Tok::Id, Tok::Plus, Tok::Id],
            vec![Tok::Id],
        ];

        let reject_strings: Vec<Vec<Tok>> = vec![
            vec![Tok::Id, Tok::Times, Tok::Lparen, Tok::Id, Tok::Plus, Tok::Rparen],
            vec![Tok::Id, Tok::Times, Tok::Lparen, Tok::Id, Tok::Id, Tok::Rparen],
            vec![Tok::Id, Tok::Times, Tok::Id, Tok::Plus, Tok::Id, Tok::Rparen],
            vec![Tok::Times, Tok::Lparen, Tok::Id, Tok::Plus, Tok::Id, Tok::Rparen],
            vec![Tok::Id, Tok::Times, Tok::Lparen, Tok::Id, Tok::Plus, Tok::Id],
            vec![Tok::Id, Tok::Id],
            vec![],
        ];

        for s in accept_strings {
            assert!(parser.parse_tokens(s).is_ok());
        }

        for s in reject_strings {
            assert!(parser.parse_tokens(s).is_err());
        }
    }

    #[test]
    fn simple_grammar2() {
        let mut parser = Parseon::<Tok, ()>::new();

        parser.set_prods(&vec![
            (Tok::S, &vec![Tok::X, Tok::S, Tok::A], None),
            (Tok::S, &vec![Tok::End], None),
            (Tok::A, &vec![Tok::X], None),
        ]);
        parser.generate_parser();
        // parser.print_action_table();

        let accept_strings: Vec<Vec<Tok>> = vec![
            vec![Tok::X, Tok::End, Tok::X],
            vec![Tok::X, Tok::X, Tok::End, Tok::X, Tok::X],
            vec![Tok::End],
        ];

        let reject_strings: Vec<Vec<Tok>> = vec![
            vec![Tok::End, Tok::End],
            vec![Tok::End, Tok::X],
            vec![Tok::X, Tok::End],
            vec![Tok::X],
            vec![],
        ];

        for s in accept_strings {
            assert!(parser.parse_tokens(s).is_ok());
        }

        for s in reject_strings {
            assert!(parser.parse_tokens(s).is_err());
        }
    }

    #[test]
    fn simple_grammar3() {
        let mut parser = Parseon::<Tok, ()>::new();

        parser.set_prods(&vec![
            (Tok::S, &vec![Tok::L, Tok::E, Tok::R], None),
            (Tok::S, &vec![Tok::R], None),
            (Tok::L, &vec![Tok::T, Tok::R], None),
            (Tok::L, &vec![Tok::P], None),
            (Tok::R, &vec![Tok::L], None),
        ]);
        parser.generate_parser();
        //parser.print_action_table();

        let accept_strings: Vec<Vec<Tok>> = vec![
            vec![Tok::T, Tok::P, Tok::E, Tok::T, Tok::P],
            vec![Tok::T, Tok::P, Tok::E, Tok::T, Tok::P],
            vec![Tok::P, Tok::E, Tok::P],
            vec![Tok::T, Tok::P],
            vec![Tok::P],
        ];

        let reject_strings: Vec<Vec<Tok>> = vec![
            vec![Tok::T, Tok::P, Tok::E, Tok::T, Tok::P, Tok::P],
            vec![Tok::T, Tok::P, Tok::E, Tok::T, Tok::E],
            vec![Tok::T, Tok::P, Tok::E, Tok::E, Tok::P],
            vec![Tok::T, Tok::P, Tok::E, Tok::T],
            vec![Tok::T, Tok::T],
            vec![],
        ];

        for s in accept_strings {
            assert!(parser.parse_tokens(s).is_ok());
        }

        for s in reject_strings {
            assert!(parser.parse_tokens(s).is_err());
        }
    }

    #[test]
    fn simple_grammar4() {
        let mut parser = Parseon::<Tok, ()>::new();

        parser.set_prods(&vec![
            (Tok::S, &vec![Tok::End], None),
            (Tok::S, &vec![Tok::First, Tok::S, Tok::Second, Tok::S], None),
            (Tok::S, &vec![Tok::First, Tok::S, Tok::Second, Tok::S, Tok::Last, Tok::S], None),
        ]);
        parser.generate_parser();
        //parser.print_action_table();

        let accept_strings: Vec<Vec<Tok>> = vec![
            vec![Tok::First, Tok::End, Tok::Second, Tok::End, Tok::Last, Tok::End],
            vec![Tok::First, Tok::End, Tok::Second, Tok::End, Tok::Last, Tok::First, Tok::End, Tok::Second, Tok::End],
            vec![Tok::First, Tok::First, Tok::End, Tok::Second, Tok::End, Tok::Second, Tok::End],
            vec![Tok::End],
        ];

        let reject_strings: Vec<Vec<Tok>> = vec![
            vec![Tok::First, Tok::End, Tok::Second, Tok::End, Tok::First, Tok::End],
            vec![Tok::First, Tok::End, Tok::Second, Tok::End, Tok::End],
            vec![Tok::First, Tok::End, Tok::Second],
            vec![Tok::First, Tok::Second, Tok::End],
            vec![Tok::End, Tok::End],
            vec![],
        ];

        for s in accept_strings {
            assert!(parser.parse_tokens(s).is_ok());
        }

        for s in reject_strings {
            assert!(parser.parse_tokens(s).is_err());
        }
    }

    #[test]
    fn simple_grammar5() {
        let mut parser = Parseon::<Tok, ()>::new();

        parser.set_prods(&vec![
            (Tok::S, &vec![Tok::A, Tok::B], None),
            (Tok::A, &vec![Tok::C, Tok::A], None),
            (Tok::A, &vec![], None),
            (Tok::B, &vec![Tok::D, Tok::B], None),
            (Tok::B, &vec![], None),
        ]);
        parser.generate_parser();
        //bovidae.print_action_table();

        let accept_strings: Vec<Vec<Tok>> = vec![
            vec![Tok::C, Tok::C, Tok::D, Tok::D],
            vec![Tok::C, Tok::D],
            vec![Tok::C, Tok::C],
            vec![Tok::D, Tok::D],
            vec![Tok::C],
            vec![Tok::D],
            vec![],
        ];

        let reject_strings: Vec<Vec<Tok>> = vec![
            vec![Tok::D, Tok::C],
            vec![Tok::C, Tok::D, Tok::C],
            vec![Tok::C, Tok::D, Tok::D, Tok::C],
        ];

        for s in accept_strings {
            assert!(parser.parse_tokens(s).is_ok());
        }

        for s in reject_strings {
            assert!(parser.parse_tokens(s).is_err());
        }
    }

    #[test]
    fn simple_grammar6() {
        let mut parser = Parseon::<Tok, ()>::new();

        parser.set_prods(&vec![
            (Tok::S, &vec![Tok::A, Tok::B, Tok::C], None),
            (Tok::A, &vec![Tok::D, Tok::A], None),
            (Tok::A, &vec![Tok::X], None),
            (Tok::B, &vec![Tok::E, Tok::B], None),
            (Tok::B, &vec![Tok::X], None),
            (Tok::C, &vec![Tok::F, Tok::C], None),
            (Tok::C, &vec![Tok::X], None),
        ]);
        parser.generate_parser();
        // parser.print_action_table();

        let accept_strings: Vec<Vec<Tok>> = vec![
            vec![Tok::D, Tok::D, Tok::X, Tok::E, Tok::E, Tok::X, Tok::F, Tok::F, Tok::X],
            vec![Tok::D, Tok::X, Tok::E, Tok::X, Tok::F, Tok::X],
            vec![Tok::D, Tok::X, Tok::X, Tok::X],
            vec![Tok::X, Tok::E, Tok::X, Tok::X],
            vec![Tok::X, Tok::X, Tok::F, Tok::X],
            vec![Tok::X, Tok::X, Tok::X],
        ];

        let reject_strings: Vec<Vec<Tok>> = vec![
            vec![Tok::D, Tok::X, Tok::D, Tok::X, Tok::X],
            vec![Tok::X, Tok::X, Tok::X, Tok::X],
            vec![Tok::X, Tok::X],
            vec![Tok::X],
            vec![],
        ];

        for s in accept_strings {
            assert!(parser.parse_tokens(s).is_ok());
        }

        for s in reject_strings {
            assert!(parser.parse_tokens(s).is_err());
        }
    }

    /*
    #[test]
    fn integration_test1() {
        let mut parser = Parseon::<Tok, TestNode>::new();

        parser.set_prods(&vec![
            (Tok::Stmts, vec![Tok::Stmt, Tok::Semi, Tok::Stmts]),
            (Tok::Stmts, vec![Tok::Stmt, Tok::Semi]),

            (Tok::Stmt, vec![Tok::Let, Tok::Id, Tok::Eq, Tok::Expr]),

            (Tok::Expr, vec![Tok::Lparen, Tok::Expr, Tok::Rparen]),
            (Tok::Expr, vec![Tok::Expr, Tok::Plus, Tok::Expr]),
            (Tok::Expr, vec![Tok::Num]),
        ]);
        parser.generate_parser();
        // parser.print_action_table();

        let tokens = vec![
            /*
            lett, id, eq, num, plus, l_paren, num, times, num, r_paren, semi, // let id = 1 + (2 * 3);
            lett, id, eq, l_paren, num, times, id, r_paren, plus, num, semi, // let id = (1 * id) + 2;
            lett, id, eq, id, semi, // let id = id;
                                    // */
        ];

        // assert!(bovidae.parse_tokens(tokens).is_ok());
        let mut idx = 0;
        while idx <= tokens.len() {
            let token = if idx == tokens.len() {
                None
            } else {
                Some(tokens[idx])
            };

            parser.parse(token);
        }
    }
*/

    /* 
    #[test]
    fn bad_grammar8() {
        let mut parser = Parseon::new();
        parser.set_prods(&vec![
            (Tok::S, vec![Tok::A]),
            (Tok::A, vec![Tok::S, Tok::E]),
        ]);
        TODO: make generate parser return an error!
        the generated action table has a state with no shift actions
        parser.generate_parser();
        parser.print_action_table();
    }
    */

    #[derive(Clone, Copy, PartialEq, Debug)]
    enum Token {
        LeftParen,
        RightParen,
        Expr,
        Plus,
        Num,
    }

    struct Node {
        token: Token,
        children: Vec<Node>,
    }

    #[test]
    fn example_usage1() {
        let mut parser = Parseon::<Token, Node>::new();

        fn addition_hook(ast_stack: &mut Vec<Node>) {
            let left_expr = ast_stack.pop().unwrap();
            let right_expr = ast_stack.pop().unwrap();
            let node = Node {
                token: Token::Plus,
                children: vec![left_expr, right_expr],
            };

            ast_stack.push(node);
        }

        fn shift_num(ast_stack: &mut Vec<Node>) {
            let node = Node {
                token: Token::Num,
                children: vec![],
            };

            ast_stack.push(node);
        }

        parser.set_prods(&vec![
            (Token::Expr, &vec![Token::LeftParen, Token::Expr, Token::RightParen], None),
            (Token::Expr, &vec![Token::Expr, Token::Plus, Token::Expr], Some(addition_hook)),
            (Token::Expr, &vec![Token::Num], None),
        ]);

        parser.shift_hook(Token::Num, shift_num);
        
        parser.generate_parser();

        let simple_expr = vec![Token::Num, Token::Plus, Token::Num];

        for token in simple_expr {
            assert!(parser.parse(token).is_ok());
        }

        let root_node = parser.accept().unwrap().unwrap();

        let left_expr = &root_node.children[0];
        let right_expr = &root_node.children[1];

        assert!(root_node.token == Token::Plus);
        assert!(root_node.children.len() == 2);
        assert!(left_expr.token == Token::Num);
        assert!(left_expr.children.len() == 0);
        assert!(right_expr.token == Token::Num);
        assert!(right_expr.children.len() == 0);
    }
}
