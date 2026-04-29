#![cfg_attr(not(debug_assertions), windows_subsystem = "windows")] // hide console window on Windows in release
#![expect(rustdoc::missing_crate_level_docs)] // it's an example

use eframe::egui;

fn main() -> eframe::Result {
    let options = eframe::NativeOptions {
        viewport: egui::ViewportBuilder::default().with_fullscreen(true),
        ..Default::default()
    };
    eframe::run_native(
        "My egui App",
        options,
        Box::new(|_cc| Ok(Box::<MyApp>::default())),
    )
}

struct MyApp {
    temperature: f64,
    program: mimir::Program,
    program_source: String,
    query: String,
}

impl Default for MyApp {
    fn default() -> Self {
        let program_source = std::fs::read_to_string("examples/fuzzy_engine.pl")
            .expect("failed to read program file");

        Self {
            temperature: 20.0,
            program: mimir::Program::new(&program_source).expect("failed to parse program"),
            program_source,
            query: String::new(),
        }
    }
}

impl eframe::App for MyApp {
    fn ui(&mut self, ui: &mut egui::Ui, _frame: &mut eframe::Frame) {
        self.query = format!("output(Heating, Cooling, {:.1})", self.temperature);
        let solutions = self.program.fuzzy_query(&self.query, 0.01);

        egui::CentralPanel::default().show_inside(ui, |ui| {
            ui.heading("Fuzzy Temperature Controller");

            ui.separator();

            ui.horizontal(|ui| {
                ui.vertical(|ui| {
                    ui.label(egui::RichText::new("Temperature").strong().underline());
                    ui.add(egui::Slider::new(&mut self.temperature, -20.0..=40.0).suffix("°C"));

                    ui.label(egui::RichText::new("Query").strong().underline());
                    ui.add(
                        egui::TextEdit::singleline(&mut format!("?- {}.", self.query).as_str())
                            .font(egui::TextStyle::Monospace),
                    );

                    ui.label(egui::RichText::new("Program").strong().underline());
                    ui.add(
                        egui::TextEdit::multiline(&mut self.program_source.as_str())
                            .font(egui::TextStyle::Monospace),
                    );
                });

                ui.separator();

                ui.vertical(|ui| match &solutions {
                    Ok(solutions) => {
                        for (i, solution) in solutions.iter().enumerate() {
                            ui.label(
                                egui::RichText::new(format!("Solution {}", i + 1))
                                    .strong()
                                    .underline(),
                            );
                            egui::Grid::new(format!("solutions_grid_{i}"))
                                .striped(false)
                                .show(ui, |ui| {
                                    for (var, value) in solution.bindings_vec() {
                                        ui.label(var);
                                        ui.label(format!("= {value}"));
                                        ui.end_row();
                                    }
                                });
                            ui.label(format!("Truth value: {:.3}", solution.truth_value()));
                        }
                    }
                    Err(err) => {
                        ui.label(format!("Error: {err}"));
                    }
                });

                ui.separator();

                ui.vertical(|ui| if let Ok(solutions) = &solutions {
                        let best = solutions
                            .iter()
                            .max_by(|a, b| a.truth_value().partial_cmp(&b.truth_value()).unwrap())
                            .unwrap();

                        ui.label(egui::RichText::new("Best Solution").strong().underline());
                        egui::Grid::new("best_solution_grid")
                            .striped(false)
                            .show(ui, |ui| {
                                for (var, value) in best.bindings_vec() {
                                    ui.label(var);

                                    if matches!(value, mimir::Value::Atom(atom) if atom == "on") {
                                        ui.label(egui::RichText::new("ON").color(
                                            egui::Color32::from_rgb(9, 185, 82)
                                        ));
                                    } else if matches!(value, mimir::Value::Atom(atom) if atom == "off") {
                                        ui.label(egui::RichText::new("OFF").color(egui::Color32::from_rgb(185, 9, 9)));
                                    } else {
                                        ui.label(format!("= {value}"));
                                    }

                                    ui.end_row();
                                }
                            });
                    }
                );
            });
        });
    }
}
