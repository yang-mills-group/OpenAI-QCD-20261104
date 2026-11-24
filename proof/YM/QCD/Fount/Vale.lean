import YM.QCD.Fount.Emit
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fount
open Function Filter Set Metric MeasureTheory Lattice Wilson Pressure RG Gauge Input Precision Tree
open Matrix Finset Push Push.Uniform Push.SectorMeasure Presented
open PhysicalNext.Repeat Lapis Sienna Lantern Bid Planned.JetPort Octave
open Next.Fluctuations Next.Fluctuations.Sector Next.SectorChange ConnectedActivityE6 Blaze Brush Poll Coat
open AbsoluteSums Fare Token Tidings Sienna QCD.Loom Fleet Cove Reggae
open scoped Topology ENNReal ContDiff BigOperators Classical Matrix.Norms.L2Operator
open Lat YM.Next.Free
open Jets.Touch Port Kit Run Bay Strut Leaf Tee Flume Garden Orbit LeafM AtomF Kings Fog Raft Transfer ParcelR Birth
variable {t a u r w b m R y p D Y C z κ d s H A δ M θ:ℝ}{L:Side}{g f h B:ℝ→ℝ}
variable {J k N l j:ℕ}
variable {c C':Side}{F:Flight J j}{e:C'.val=c.val*F.L.val}
variable {S:StepData c C'}{T:Forest S.ratio}{ρ: Bid.Dir su c→AxisChart su T}
local notation "Z"=>Lapis.orbit T ρ
local notation "Vp"=> (fun i:Positions (Primary c su)=> represent (Uniform.tint su _ i))
lemma offerK {Bq:ℕ}{V:Grid c→Sheet c}{X:Grid C'→Sheet C'}(hp:Species F e C R t 0 p l X)(hv:Species F e C R t 0 p l (houseK m X))(hs:Own c δ 0 Bq V D)(hD:0≤D)(hδ:0<δ)(ht:0<t)(h0:|m| ≤ d)(he:d*R ≤ 1/2)(hs':0<s)(W:ℕ→Atom su 2)(N:ℕ)(hg:1 ≤ k) (hP: PaintSupply su k z)(hw:∀ y,‖y‖<u→Brush k M 1 (Z) y)(hz:ρ 0=0)(hA:u≤1)(hK:M*u≤1){x:Positions (Primary c su)}(hx:‖x‖<u)(hy: (Fintype.card (Site C'):ℝ)≤ w)(hh:(Fintype.card (Modes c N):ℝ) ≤ a):
   let T':= amber m s X V F e N W ρ; ContDiffAt ℝ k T' x ∧ normJ k T' x≤ rose z t δ M w D R d s a k N:=by
    intro T'; obtain ⟨hz,hx'⟩:= lampA hg hw hz hA hK hx k le_rfl; obtain ⟨c',hc⟩:=lively hp hv ht h0 he s hs' W N hP _ hx' hy hh hg
    let U := fun _ : Positions (Primary c su)=>baker c N c'; have hv:=(((portrait hs hδ hD (stove hP (hx.le.trans hA))).report _ ((billed hs' c N).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hh _) (sq_nonneg _)))).smul m)
    have hg':0 ≤ a:= (Nat.cast_nonneg _).trans hh; have ht₀ := (composite hz hc).separating (hv.climb (mul_le_mul_of_nonneg_right h0 ?_) le_rfl); rotate_left
    · exact (mul_nonneg (by positivity) (portrait hs hδ hD (stove hP (hx.le.trans hA))).nonneg)
    have hp': Brush k (rose z t δ M w D R d s a k N) 1 (T'-U) x := ht₀.shimmy (Eventually.of_forall fun x=>?_)
    swap; · dsimp only [amber,T',favor,Pi.sub_apply,Pi.smul_apply, Function.comp_apply,U]; abel
    have ht:= hp'.smooth.add (g:=U) contDiffAt_const
    change ContDiffAt ℝ k ((T'-U)+U) x at ht; rw [sub_add_cancel] at ht
    refine ⟨ht,?_⟩; apply Eq.trans_le ?_ ((Brush.offer.1 hp').2 _ le_rfl)
    obtain ⟨k,rfl⟩:= Nat.exists_eq_succ_of_ne_zero (show k≠0 by omega); unfold normJ; rw [iteratedFDeriv_sub_apply ht contDiffAt_const]; rw [iteratedFDeriv_succ_const,Pi.zero_apply,sub_zero]
-- Value at flat purely small. Avoid alpha multiplier.
lemma projects {V:Grid c→Sheet c}{X:Grid C'→Sheet C'}(hp:Species F e C R t 0 p l X)(hv:Species F e C R t 0 p l (houseK m X))(ht:0<t)(hM: V 1=leftL F e X 1*rightL F e X 1) (hρ:ρ 0=0)(W:ℕ→Atom su 2)(N:ℕ)(hs:0<s)(h0:|m| ≤ d)(hh:(Fintype.card (Modes c N):ℝ) ≤ a):
    ‖amber m s X V F e N W ρ 0‖ ≤ (s^2*a^2)*(d^2*(R*R*R)):=by
    have hz:Vp 0=1:=by simp only [map_zero]; simp
    have he: Octave.projection T (0,Z 0)= (1:Grid C'):=by
       simp only [Lapis.orbit, Uniform.station,Function.comp_apply,map_zero,hρ]; change Uniform.fine su T (combineH T 0)=_; rw [map_zero]; exact (fine_supply T (paint_supply su 0).choose_spec).1
    have hk:amber m s X V F e N W ρ 0=powerZ c N s (burr m X F e 1):=by
       unfold amber favor; simp only [he,hz,Pi.sub_apply]; unfold Octave.tonic mica Function.comp; simp only [map_add, sub_self]; rw [hM,map_sub]; -- edit
       unfold uplift; rw [Pi.sub_apply, map_sub]; rw [add_sub_add_left_eq_sub, show powerZ c N s ((m:ℂ) • (leftL F e X 1 * rightL F e X 1)) = m • powerZ c N s _ from map_smul (powerZ c N s) m _]; exact rfl
    rw [hk]; have hu:‖powerZ c N s‖ ≤ s^2*a^2:= (billed hs ..).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hh _) (sq_nonneg _)); have he:=hp.forest
    apply ((powerZ c N s).le_opNorm _).trans; exact mul_le_mul hu ((unfelt ht hp hv le_rfl).2 _|>.trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg m) h0 _) (by positivity))) (norm_nonneg _) (by positivity)
end YM.QCD.Fount
