import YM.QCD.Eyrie.Dredge

/-!
# score birth on critical (all periods, orientation forest independent from Gala).
After-L, NOT inheritance estimate. Real jets for every vertex paths.
-/
set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 40000
namespace YM.QCD.Eyrie
open Function Filter Lattice Wilson Lat Kit Cost Finset Run Revolve Metric Push.Uniform
open Quarry Tree RG Precision Rudder Flume Pine YM.Next.Free
open scoped Topology Matrix Matrix.Norms.L2Operator BigOperators Classical ContDiff
variable {T : Type*} {X : Works T} {j k N m:ℕ} {W : T→Flight j k}
variable {a' C' : ℝ} {O : KernelChoices} {P : Patch} {p:Clip} {M : Before su a' C' P.J O N}
lemma Works.League.group {T I: Type*} [Fintype I]{P:Works T}{A B:Bool}{M:I→ P.Board A B}{s:Finset I}(h:∀ i∈s,P.League (M i)):
    P.League (A:=A) (B:=B) (fun i x=>∑ j∈s,M j i x):=by
  induction s using Finset.induction_on with
  | empty=> simp only [sum_empty]; exact Works.League.zeros P A B
  | insert a s ha ih=> simp_rw [sum_insert ha]; exact (h _ (mem_insert_self ..)).plus (ih fun i hi=> h i (mem_insert_of_mem hi))
-- universe issue Fleet works different universe? check
lemma Works.League.tax {A B: Bool}{F:X.Board A B}(h:X.League F) (c:ℂ):X.League (A:=A) (B:=B) (fun i x=> c • F i x):=by
  obtain ⟨t,d,h,h',H⟩:=h; exact ⟨_,_,h,show 0≤4*(‖c‖*d) from by positivity,fun i=> (H i).tariff c⟩
variable {V: T→Flight j k}
namespace Quay
variable (Q:Quay X O P p M)
variable (h : ∀ y, (V y).patch=P)
include Q
lemma rotor (w:Walk) : X.League (A:=true) (B:=true) (fun y x=> routeM 0 (Q.forge y x) w):=by
  let B : Gleam:=⟨w,(1:Spike)⟩
  have hv : Wages 1 (B.rate 1) (fun _ : Unit=>B):=⟨zero_le_one,Summable.of_finite,by simp⟩
  have ht:= Q.dustborne (fun _ _ => queen B) zero_lt_one fun _=> trek hv
  apply ht.knows; intro i; refine Eventually.of_forall fun x=> ?_ ; unfold dust; simp [queen_rides,Gleam.dept,B,on_spin_one]
lemma pitcher : X.League (A:=false) (B:=true) (fun i _=>scoop (X.ratio i)):=by
  refine ⟨1,1,zero_lt_one,zero_le_one,fun y i j=>?_⟩
  apply (Flock.hush _ zero_lt_one).patron; change ‖scoop (X.ratio y) _ _‖ ≤ _
  simp only [scoop,Matrix.of_apply]; split
  next hh => subst j; change ‖(1:ℂ)‖≤1*Decay 1 _ ((X.ratio y).embed i.1); unfold Works.origin; simp [Decay]
  rw [norm_zero,one_mul]; exact (Push.Uniform.decay_pos ..).le

include h
lemma patches (i): (V i).L=P.L:=congr_arg Patch.L (h i)
lemma ratio_info (i:T) : (X.n i).val=(X.s i).val*(V i).L.val:=by rw [Q.patches h i]; exact Q.ideology _
def monies (i:T): Grid (X.n i)→Kit.Rail (X.s i) (X.n i):= tied (V i) (Q.ratio_info h i) 0
lemma checks (i z) : Q.monies h i (Q.forge i z) = (massL P.L:ℂ) • ((votes:ℂ)⁻¹ • ∑ o:Lattice.Order, ∑ a:P.Points, (P.weight a:ℂ) • (scoop (X.ratio i)*routeM 0 (Q.forge i z) (route 0 a.val o))):=by
  unfold monies tied lineF
  have hr {a b : Lattice.Ratio (X.s i) (X.n i)} (h:a.count=b.count):a=b := by cases a; cases b; congr
  have ht: sliceL (V i) (Q.ratio_info h i) = X.ratio i:=hr ((Q.patches h i).trans (Q.alignment i).symm)
  rw [show (V i).L=P.L from Q.patches h i] -- dependent rewrites
  simp_rw [ht]; rw [h i]
lemma moors : X.League (A:=false) (B:=true) (fun i x=>Q.monies h i (Q.forge i x)):=by
  simp_rw [Q.checks h]
  refine Works.League.tax (Works.League.tax ?_ _) _
  refine Works.League.group (P:=X) (A:=false) (B:=true) (M:=fun (o:Lattice.Order) i z=> ∑ a:P.Points,(P.weight a:ℂ) • (scoop (X.ratio i)*routeM 0 (Q.forge i z) (route 0 a.val o))) ?_
  intro o _
  apply Works.League.group (P:=X) (A:=false) (B:=true) (M:=fun (a:P.Points) i z=>(P.weight a:ℂ) • (scoop (X.ratio i)*routeM 0 (Q.forge i z) (route 0 a.val o)))
  intro a _; exact (Q.pitcher.connects (Q.rotor (route 0 a.val o))).tax _
lemma referee (B:Plan j): X.League (A:=true) (B:=true) (fun i x=>vaultF B (V i) (Q.ratio_info h i) 0 (Q.forge i x)):=by
  exact (Q.woodhouse B _).plus ((Q.moors h).up.connects (Q.moors h))
lemma residents (B : Plan j): X.League (A:=true) (B:=true) (fun y _=> (vaultF B (V y) (Q.ratio_info h y) 0 1)⁻¹):=by
  obtain ⟨w,z,g,R,δ,Y,m,H⟩:=groves B P.L k zero_le_one
  refine ⟨amplitude m,offerZ w R g,amplitude_pos _, offerZ0 H.pays.le H.solid.le H.pos,fun i j v=>?_⟩
  apply (Flock.hush _ (amplitude_pos _)).patron
  have hh:=H.returnable (V i) (Q.patches h i) (Q.ratio_info h i) zero_le_one (le_refl m) (0:Site (X.n i))
  exact purchases hh H.tube ..
variable {U : ∀ y:T, Grid (X.n y)→Sheet (X.n y)}
lemma citizens (B:Plan j)(hF:X.League (A:=true) (B:=true) (fun i x=> U i (Q.forge i x)))(hz : ∀ i,U i 1=0):
    X.League (A:=true) (B:=true) fun y x=> ((vaultF B (V y) (Q.ratio_info h y) 0 (Q.forge y x)+ U y (Q.forge y x))⁻¹):=by
  have he i : vaultF B _ (Q.ratio_info h i) 0 (Q.forge i 0)+U i (Q.forge i 0)=vaultF B (V i) (Q.ratio_info h i) 0 1:=by rw [forge0,hz,add_zero]
  exact Works.League.invert (P:=X) (A:=true) _ ((Q.referee h B).plus hF) (fun i=> by erw [he i]; exact ticket_inv ..) (Works.League.knows (Q.residents h B) (fun i=> Eventually.of_forall fun x=> congr_arg Inv.inv (he i)))
end Quay
end YM.QCD.Eyrie
