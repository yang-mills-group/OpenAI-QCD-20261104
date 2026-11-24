import YM.Mural.Facts
open Classical
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Apron
open ConnectedActivityE6 QCD
open Function Lattice Wilson Tree RG Pressure Finset Filter MeasureTheory Pressure.Stores
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open Mixed Reserves Trees QCD.Beam QCD.Beam.Pipe QCD.Cove QCD.Leaf Lat Creek Loom Loom.Fleet
open QCD.Leaf QCD.Jets Fj Further.ShellBirth49.Fusing Collide QCD.Jets.Touch
open Kit Fork QCD.Port Flume YM.Next.Free QCD.Leaf Tee QCD.Orbit Quarry Garden Footprint Bay Run QCD.Jets.Sun Pine Grass
open Patron Blaze King March GasP Ursell QCD.Stew Stained
open Sway OrbitG Ribbon QCD.Mural
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {c f L:Side}{S:StepData c f}{T:Tube su S}{P:Teller su}{β τ C μ W:ℝ}
variable {R:Rep su f}{O:BudgetPoint}{F:Tree.Forest S.ratio}{Q:Target su P}{o:Target.Order su W}
variable {H:Cash W τ μ L Q o C T R}{ι κ I E J D:Type}{N:ℕ}
open QCD.Mural NormedSpace Stitch Plate PaletteT Grove
variable (Y:Fleet H ι N)(p:Unit→Site c)(φ:ℝ){v h b:ℝ} {n:ℕ} (t:ℝ)
lemma ticket_at (x:EvenA c N)(hv:0<φ) : premiumG c N Unit φ t n (bearing Unit c N x) = ‖paidM (univ:Finset (Keys c N)) t n φ x‖:=by
   let y:= precept x Unit; have hf:Polite (fun _:Unit=>false) ∅ y:=by unfold Polite; rw [burst_absent]; exact ⟨x.val,quiet ..⟩
   rw [← braces Unit (fun _=> (0:Site c)) x φ,pennedM c _ _ _ φ t _ hv _ hf,attachedM c N Unit φ t _ hv _ hf]
   let s:Finset (Spine Unit):= ∅; have h: scrape (Keys c N) s y.val=x.val:=by change scrape _ s (fiber (Spine Unit) x.val)=_; rw [← quiet, show s=∅ from rfl, quid]
   rw [burst_absent]; exact congr_arg _ h
variable (N₀:ℕ) (J:ι→Site c) {A:ι→ℝ} {X:Finset ι} {n₀ n₁:ℕ}{ψ:ι→Grid f→ Grid c→EvenA c N}
lemma lay_v (X:Coat T F)(i:ι)(z:Air f su)(hp:0<φ) : ‖paidM (family c N Unit) t n φ ((loommark Unit Y).coming i X z)‖= ‖paidM (univ:Finset (Keys c N)) t n φ (Y.coming i X z)‖:= by rw [show (loommark Unit Y).coming i X z= bearing Unit c N (Y.coming i X z) from ((bearer Unit c N).map_smul (Y.riseP X z i) (Y.works i _ X.V)).symm]; exact ticket_at φ t _ hp
variable {r:ℝ}
lemma serveV (hv:Vigil Y univ F J A t n φ v X n₀ n₁)(hp:0<φ) : Vigil (loommark Unit Y) (family c N Unit) F J A t n φ v X n₀ n₁:=⟨hv.grow,hv.rise,hv.seat,fun i U he ht hh z hp'=> by rw [lay_v Y φ t U i z hp] at hp'; exact hv.rare i U he ht hh z hp',fun i U he ht hh z=> Eq.trans_le (lay_v Y φ t U i z hp) (hv.cover i U he ht hh z)⟩
open Glow
lemma forgeV (h: Stern Y F univ J A φ v X n₀ n₁ ψ)(he:Ac.Hit Y.ground (radiusB τ) (fun i=>Real.exp 1*A i) Q.relative (phaseR L τ))(hx: t^2*phaseR L τ ≤ fundsL L r τ)(hp:0<φ)(hz: t^4*Real.exp v ≤ Real.exp b)(ht:1 ≤ t)(hG:∀ i,(Y.ground i).Nonempty)(hm:fundsL L r τ≤1) : ∃ w,Vigil (loommark Unit Y) (family c N Unit) F J w t 4 φ b X n₀ n₁∧ Ac.Hit (loommark Unit Y).ground (radiusB τ) w Q.relative (fundsL L r τ):=by
    let w i:= t^2*(Real.exp 1*A i); have hh i:0 ≤ w i:=mul_nonneg (sq_nonneg _) (mul_nonneg (Real.exp_pos _).le (h.wage i))
    have ht' : Ac.Hit Y.ground (radiusB τ) w Q.relative (fundsL L r τ):=fun i=> budget_loosen (heights_factor _ _ _ w he (fun _=>rfl) (sq_nonneg t) i) hx
    have hf:0 ≤ Q.relative:=by unfold Target.relative; linarith only [Q.bound,Q.pos,Q.usable]
    refine ⟨w,serveV Y φ t J (seasoned Y univ h hp ht hz (fun i=>?_)) hp, ht'⟩
    obtain ⟨j,hV⟩:=hG i; have h0:=budget_sum (ht' j) {i}; rw [sum_singleton,if_pos hV] at h0
    exact ((mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (h.wage i) (Real.one_le_exp (by norm_num))) (sq_nonneg t)).trans (le_mul_of_one_le_right (hh i) (Real.one_le_exp (mul_nonneg hf (Nat.cast_nonneg _))))).trans (h0.trans hm)
end YM.MassiveQCD.Apron
#print axioms YM.MassiveQCD.Apron.forgeV
