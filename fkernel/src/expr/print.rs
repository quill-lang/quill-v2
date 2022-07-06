use std::collections::HashMap;

use fnodes::{expr::*, universe::*, SexprParser};

use super::instantiate;

/// A utility for printing values to screen.
/// Works like the Display trait, but works better for printing type variable names.
pub struct ExprPrinter<'a> {
    db: &'a dyn SexprParser,
    /// Maps inference variables to the names we use to render them.
    metavariable_names: HashMap<Metavariable, String>,
    /// When we see a new inference variable that we've not named yet, what name should we give it?
    /// This monotonically increasing counter is used to work out what the name should be.
    next_metavariable_name: u32,
    /// Like [`Self::metavariable_names`] but for universes.
    metauniverse_names: HashMap<Metauniverse, String>,
    /// Like [`Self::next_metavariable_name`] but for universes.
    next_metauniverse_name: u32,
}

impl<'a> ExprPrinter<'a> {
    pub fn new(db: &'a dyn SexprParser) -> Self {
        Self {
            db,
            metavariable_names: HashMap::new(),
            next_metavariable_name: 0,
            metauniverse_names: HashMap::new(),
            next_metauniverse_name: 0,
        }
    }

    pub fn print_universe(&mut self, val: &Universe) -> String {
        match &val.contents {
            UniverseContents::UniverseZero => "0".to_string(),
            UniverseContents::UniverseVariable(var) => self.db.lookup_intern_string_data(var.0),
            UniverseContents::UniverseSucc(succ) => {
                format!("{} + 1", self.print_universe(&succ.0))
            }
            UniverseContents::UniverseMax(max) => format!(
                "max ({}) ({})",
                self.print_universe(&max.left),
                self.print_universe(&max.right)
            ),
            UniverseContents::UniverseImpredicativeMax(imax) => {
                format!(
                    "imax ({}) ({})",
                    self.print_universe(&imax.left),
                    self.print_universe(&imax.right)
                )
            }
            UniverseContents::Metauniverse(metauniverse) => {
                format!("universe_{}", self.get_metauniverse_name(*metauniverse))
            }
        }
    }

    pub fn print(&mut self, val: &Expr) -> String {
        match &val.contents {
            ExprContents::Bound(bound) => bound.index.to_string(),
            ExprContents::Lambda(lambda) => {
                let contents = format!(
                    "{} : {}",
                    self.db
                        .lookup_intern_string_data(lambda.parameter_name.contents),
                    self.print(&lambda.parameter_ty)
                );
                let binder = match lambda.binder_annotation {
                    BinderAnnotation::Explicit => format!("({})", contents),
                    BinderAnnotation::ImplicitEager => format!("{{{}}}", contents),
                    BinderAnnotation::ImplicitWeak => format!("{{{{{}}}}}", contents),
                    BinderAnnotation::ImplicitTypeclass => format!("[{}]", contents),
                };
                let mut body = *lambda.result.clone();
                instantiate(
                    &mut body,
                    &Expr::new_synthetic(ExprContents::LocalConstant(
                        lambda.generate_local(&mut MetavariableGenerator::new(None)),
                    )),
                );
                format!("λ {}, {}", binder, self.print(&body))
            }
            ExprContents::Pi(pi) => {
                let contents = format!(
                    "{} : {}",
                    self.db
                        .lookup_intern_string_data(pi.parameter_name.contents),
                    self.print(&*pi.parameter_ty)
                );
                let binder = match pi.binder_annotation {
                    BinderAnnotation::Explicit => format!("({})", contents),
                    BinderAnnotation::ImplicitEager => format!("{{{}}}", contents),
                    BinderAnnotation::ImplicitWeak => format!("{{{{{}}}}}", contents),
                    BinderAnnotation::ImplicitTypeclass => format!("[{}]", contents),
                };
                let mut body = *pi.result.clone();
                instantiate(
                    &mut body,
                    &Expr::new_synthetic(ExprContents::LocalConstant(
                        pi.generate_local(&mut MetavariableGenerator::new(None)),
                    )),
                );
                format!("Π {}, {}", binder, self.print(&body))
            }
            ExprContents::Apply(apply) => {
                format!(
                    "({}) ({})",
                    self.print(&apply.function),
                    self.print(&apply.argument)
                )
            }
            ExprContents::Sort(Sort(universe)) => {
                if let Some(n) = universe.to_explicit_universe() {
                    match n {
                        0 => "Prop".to_string(),
                        1 => "Type".to_string(),
                        2 => "Kind".to_string(),
                        _ => format!("Sort {}", n),
                    }
                } else {
                    format!("Sort ({})", self.print_universe(universe))
                }
            }
            ExprContents::Inst(inst) => inst.name.display(self.db.up()),
            ExprContents::Let(_) => todo!(),
            ExprContents::Metavariable(_) => todo!(),
            ExprContents::LocalConstant(local) => {
                format!(
                    "{}",
                    self.db.lookup_intern_string_data(local.name.contents),
                    // self.print(&local.metavariable.ty)
                )
            }
        }
    }

    fn get_metavariable_name(&mut self, var: Metavariable) -> String {
        if let Some(result) = self.metavariable_names.get(&var) {
            result.clone()
        } else {
            let name = self.new_metavariable_name();
            self.metavariable_names.insert(var, name.clone());
            name
        }
    }

    fn get_metauniverse_name(&mut self, var: Metauniverse) -> String {
        if let Some(result) = self.metauniverse_names.get(&var) {
            result.clone()
        } else {
            let name = self.new_metauniverse_name();
            self.metauniverse_names.insert(var, name.clone());
            name
        }
    }

    fn new_metavariable_name(&mut self) -> String {
        let id = self.next_metavariable_name;
        self.next_metavariable_name += 1;

        // Assign a new lowercase Greek letter to this type.
        // There are 24 letters to choose from.
        // If we overflow this, just add a suffix to the name.
        let name = std::char::from_u32('α' as u32 + (id % 24)).unwrap();
        let suffix = id / 24;
        if suffix > 0 {
            format!("{}{}", name, suffix)
        } else {
            format!("{}", name)
        }
    }

    fn new_metauniverse_name(&mut self) -> String {
        let id = self.next_metauniverse_name;
        self.next_metauniverse_name += 1;
        id.to_string()
    }
}
