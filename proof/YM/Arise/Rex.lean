import YM.Arise.Mica
import YM.Massive.Target.Wick
/-! # signed rhythm for spin as multipole, both directions. -/
set_option autoImplicit false
noncomputable section
namespace YM.Arise
open Function Lattice Finset Wilson Filter MeasureTheory Tensor Work.G06 RG Massive Massive.UV UV.Free
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
variable {r n m i j l k d:ℕ}
variable {F :Type*}[NormedAddCommGroup F][NormedSpace ℝ F]
variable {G:Gauge}
variable (s t: Signed)(x y:Cover)(a b:Axis)(p:PlaqAxes)(U:CoverConfig G)
variable (z:Cover) (l: List Axis)
lemma spine_cost (u:Multi d) : (steps u).length = UV.order (power u):=by unfold UV.order steps; simp [List.finRange,Fin.sum_univ_succ]
lemma spine_code (u:Multi d)(a:Axis): (steps u).count a=power u a:=by unfold steps; rw [List.count_flatMap]; simp [List.count_replicate,List.finRange]; rcases (show a=0∨a=1∨a=2∨a=3 from (by decide : ∀ i: Axis,i=0∨i=1∨i=2∨i=3) a) with rfl|rfl|rfl|rfl <;> (norm_num [show (2:Axis) ≠ 0 from by decide, show (3:Axis)≠0 from by decide,show (2:Axis)≠3 from by decide,show (3:Axis)≠2 from by decide,show (2:Axis)≠1 from by decide,show (3:Axis)≠1 from by decide , show (0:Axis)≠2 from by decide, show (0:Axis)≠3 from by decide, show (1:Axis)≠2 from by decide, show (1:Axis)≠3 from by decide])
def gybe (s: Signed)(u:Multi d): Multi d:=⟨u.val∘ s.perm.symm,by rw [UV.order,← Equiv.sum_comp s.perm]; simp only [Function.comp_apply,Equiv.symm_apply_apply]; exact u.property⟩
lemma gybe_one (u:Multi d): gybe 1 u=u:=rfl
lemma gybe_mul (u:Multi d): gybe (s*t) u=gybe s (gybe t u):=rfl
lemma gybe_code (u:Multi d)(i: Axis) : power (gybe s u) (s.perm i)=power u i:=by simp [power,gybe]
lemma gybe_steps (u:Multi d): List.Perm (steps (gybe s u)) (sways s (steps u)) :=by
    refine List.perm_iff_count.mpr (fun i=>?_); obtain ⟨i,rfl⟩:=s.perm.surjective i; unfold sways; rw [spine_code, List.count_map_of_injective _ _ s.perm.injective, spine_code, gybe_code]
def limns (s:Signed)(p:Multi d):=vane s (steps p)
lemma l_step (u:Multi d): limns (s*t) u=limns s (gybe t u)*limns t u:=by unfold limns; rw [vane_mul]; unfold vane; exact congr_arg (· * _) (((gybe_steps t u).map _).prod_eq).symm
lemma l_pin (u:Multi d): limns s u*limns s u=1:=vane_sq ..
lemma l_start (u:Multi d): limns 1 u=1:= vane_id _
lemma strike_perm (l l':List Axis)(h:l.Perm l') : strike l x=strike l' x:=by
   induction h generalizing x with
   | nil=> rfl
   | cons a h ih=> rw [strike,strike,ih,ih]
   | swap a b l=> rw [strike,strike,strike,strike,strike,strike,add_right_comm x (step a)]; abel
   | trans h g ih ig=> exact (ih x).trans (ig x)
lemma Rocky.perm (p:Option PlaqAxes)(l l':List Axis)(h:l.Perm l')(X:Parc)(hp:Rocky p l n X): Rocky p l' n X:=by
    constructor
    · rw [←strike_perm 0 _ _ h,← h.length_eq]; exact hp.rest
    intro k ha hk; rw [← h.length_eq] at hk; exact hp.stops k ha hk
noncomputable def torch (s:Signed) : Rhythm→ₗ[ℝ] Rhythm:= hears fun w=> Finsupp.single (tap s w) 1
lemma tap_mul (w:Walk): tap (s*t) w=tap s (tap t w):=by induction w with|nil=>rfl|cons a w ih=>change (a.rotate _ :: tap _ w)= _; rw [← Step.rotate_mul,ih]; rfl
lemma tags (W:Rhythm): torch (s*t) W=torch s (torch t W):=by induction W using Finsupp.induction_linear with|zero=>simp|add u v h hp=>rw [map_add,map_add,map_add,h,hp]|single i a=>simp [torch,tap_mul,hears]
lemma burst (W: Rhythm): came (torch s W)=stake s 0 (came W):=by induction W using Finsupp.induction_linear with|zero=>simp|add u v h hp=>rw [map_add,map_add,map_add,map_add,h,hp]|single i a=> simp only [torch,came,stake,hears,Finsupp.linearCombination_single,map_smul]; have ht:= hale_last s i (0:Cover); simp only [Signed.act_zero] at ht; unfold tap; simp [ht]
noncomputable def tassels (s:Signed)(u:Multi d):=let v:=gybe s⁻¹ u; limns s v • torch s (song d (steps v) none)
noncomputable def rider (u:Multi d) : Rhythm:= (Fintype.card Signed:ℝ)⁻¹ • ∑ i:Signed,tassels i u
lemma rideOn(u:Multi d): Rocky none (steps u) d (came (rider u)):=by
    rw [rider,map_smul,map_sum]; refine Rocky.mean _ _ _ _ (fun i=>?_); let v:=gybe i⁻¹ u; have ht:gybe i v=u:=by unfold v; rw [← gybe_mul,mul_inv_cancel,gybe_one]
    change Rocky _ _ _ (came (limns i v • torch i _)); rw [map_smul,burst]; refine Rocky.perm _ (sways i (steps v)) _ (by simpa only [ht] using (gybe_steps i v).symm) _ (earned i _ none _ (soundR ..) ((spine_cost v).trans_le v.property))
lemma rideE (u:Multi d): rider (gybe s u)=limns s u • torch s (rider u):=by
     have hp (i:Signed): tassels (s*i) (gybe s u)=limns s u • torch s (tassels i u):=by
            let v:=gybe i⁻¹ u; have hv:gybe (s*i)⁻¹ (gybe s u)= v:=by rw [mul_inv_rev, ← gybe_mul,mul_assoc,inv_mul_cancel,mul_one]
            have ht:gybe i v=u:=by unfold v; rw [← gybe_mul,mul_inv_cancel, gybe_one]
            unfold tassels; dsimp only; rw [hv,l_step,ht,tags,mul_smul,map_smul]
     unfold rider; rw [← Equiv.sum_comp (Equiv.mulLeft s) (fun i=>tassels i (gybe s u)),map_smul,map_sum, smul_comm (limns s u) (↑(Fintype.card Signed):ℝ)⁻¹]; conv_rhs=> rw [smul_sum] -- syntax!
     exact congr_arg ((↑(Fintype.card Signed):ℝ)⁻¹ • ·) (sum_congr rfl fun i _=>hp i)
lemma riding (u:Multi d):came (rider (gybe s u))=limns s u • stake s 0 (came (rider u)):=by rw [rideE,map_smul,burst]
end YM.Arise
#print axioms YM.Arise.rideE
#print axioms YM.Arise.rideOn
