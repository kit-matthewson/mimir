#set table(
  stroke: (_, y) => (
    top: if y <= 1 { 1pt } else { 0pt },
    bottom: 1pt,
  ),

  fill: (_, row) => if calc.even(row) and row > 0 {
    luma(95%)
  } else {
    none
  },

  inset: (y: 4pt),
)

#show table.cell.where(y: 0): set text(weight: "bold")
#set table.hline(stroke: 0.5pt)

= ECM3401 Project Logbook

*Student Name:* Kit Matthewson \
*Project Name:* An Implementation of Prolog in Rust \
*Internal Supervisor:* Dr. Soufian Majeed

#table(
  columns: 4,
  [Date], [Key Activities], [Outcomes], [Comments],
  [26/09/2025], [], [], [],
  [03/10/2025], [], [], [],
  [10/10/2025], [], [], [],
  [17/10/2025], [], [], [],
  [24/10/2025], [], [], [],
  [07/11/2025], [], [], [],
  [14/11/2025], [- Discussed final draft of literature review.], [- Happy to submit the final draft for marking.], [],
  [21/11/2025], [], [], [],
  [28/11/2025], [], [], [],
  [05/12/2025], [], [], [],
  [11/12/2025],
  [
    - Discussed literature review feedback.
    - Agreed on work to do over Christmas.
  ],
  [],
  [],

  [16/01/2026],
  [- Discussed progress over the Christmas holiday.],
  [- Agreed to focus more on the report for a while, instead of the programming side.],
  [],

  [23/01/2026],
  [
    - Looked at mark scheme for final report.
    - Reviewed plan for the final report.
  ],
  [- Agreed to go ahead with the general plan.],
  [],
)
