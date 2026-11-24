import YM.QCD.Dust.Harps
/-! # stellar beam correction paid on old-height input, after-L at test one, independent n. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Dust
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run Brick
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Garden Fork Leaf Tee Flume YM.Next.Free Laurent Reggae
open PhysicalNext.JointLoad MultiNext.SignedSource
variable {c f L:Side} {j k N n:ℕ} {C h1 h2 u v w t:ℝ} {o:Site f}{p r:ℝ}{K:Kit.Rail f c}
local notation "A"=> Crate f N
local notation "X" => Keys f N
lemma uplifts (h:0<t): Function.Bijective (bias (Stew.lens (N:=N) o) t):=by
   rw [← ContinuousLinearMap.coe_coe]; apply and_iff_left_of_imp (fun h : Injective ((bias (Stew.lens (N:=N) o) t).toLinearMap)=> LinearMap.surjective_of_injective h)|>.mpr -- overlap
   intro x y he; apply Stew.poster; intro i; have hx:= congr_arg (coef i) he; change coef i (bias _ _ x)=coef i (bias _ _ y) at hx; simp only [tile] at hx; exact mul_left_cancel₀ (by unfold starch pieD; norm_cast; positivity) hx
noncomputable def rave (o:Site f)(N:ℕ)(t:ℝ)(h:0<t): Crate f N≃L[ℂ]Crate f N:= LinearEquiv.toContinuousLinearEquiv (LinearEquiv.ofBijective _ (uplifts (N:=N) (o:=o) h))
def merchant (a:Site c) (o:Site f)(S:Kit.Rail f c)(u t :ℝ)(ht:0<t) (Y:Rune f) (N:ℕ):Crate f N →L[ℂ] Crate c N:= ((bias (Stew.lens a) u).comp (((apple S N).comp (changeVars (tor Y))).toLinearMap.toContinuousLinearMap)).comp ((rave o N t ht).symm: Crate f N≃L[ℂ] Crate f N).toContinuousLinearMap
variable {a:Site c} (g: Rune f)
lemma commerce (ht:0<t)(x:A): merchant a o K u t ht g N (bias (Stew.lens o) t x)= bias (Stew.lens a) u (apple K N (changeVars (tor g) x)) :=by unfold merchant; simp only [ContinuousLinearMap.comp_apply]; rw [show (rave o N t ht).symm.toContinuousLinearMap (bias (Stew.lens o) t x)=x from (rave o N t ht).symm_apply_apply x]; rfl
lemma torchlight (i:A): ContDiff ℂ ω (fun g:Rune f=> changeVars (tor g) i):=by
   have hs (l:List X): ContDiff ℂ ω (fun g:Rune f=> changeVars (tor g) (l.map atom).prod):=by
      induction l with
      | nil=> simp only [List.map_nil,List.prod_nil,map_one]; exact contDiff_const
      | cons i l ih=> simp only [List.map_cons,List.prod_cons,map_mul]; apply ContDiff.mul _ ih; simp_rw [change_atom]; exact ContDiff.sum fun j _=> (torch i j).smul (contDiff_const (c:= atom j)) -- name
   rw [← write i]; simp_rw [map_sum,map_smul]; apply ContDiff.sum; intro s _; obtain ⟨v,-,-,hv⟩:= Grass.expression s; rw [hv]; exact ContDiff.smul (contDiff_const (𝕜:=ℂ) (c:=coef s i)) (by simpa only [List.map_ofFn] using hs (List.ofFn v))
lemma stupor (ht:0<t): ContDiff ℂ ω (fun g:Rune f=> merchant a o K u t ht g N):=by refine contDiff_clm_apply_iff.mpr fun i=>?_ ; exact (bias (Stew.lens a) u).contDiff.comp ((((apple K N).toLinearMap.toContinuousLinearMap).contDiff).comp (torchlight ((rave o N t ht).symm i)))
lemma creditB (hp:0<p)(hr: 0<t)(hv:0 < v)(he:‖g‖ ≤v)(hf:fareG v p N ≤ t)(h:∀ i:A,Stew.plank a u (apple K N i) ≤ Stew.plank o p i): ‖merchant a o K u t hr g N‖ ≤1:=by
   apply ContinuousLinearMap.opNorm_le_bound _ (show (0:ℝ)≤1 from zero_le_one); intro z; obtain ⟨x,rfl⟩:= (uplifts (N:=N) (o:=o) hr).2 z; rw [commerce,one_mul]; exact (h _).trans (stems g he hv hp hf x)
lemma royal (k:Frame f): ‖ramp f k‖ ≤1:=by
    have hh(j:Site f → su.El): ‖(fun i=>Lat.touch (colour (j i)))‖≤1:=(pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun i=> Lat.rotation_price (touch_u (j i).1.property))
    exact max_le (hh k) (hh k⁻¹)
def pulseQ (f:Side)(V:Site f→su.Color): Rune f:= ramp f fun i=>su.lieExp (V i)
lemma holy (x:A): changeVars (tor (pulseQ f 0)) x=x:=by
   have ht:pulseQ f 0 = (fun _=>(1:Bundle),fun _=>(1:Bundle)):=by unfold pulseQ ramp; simp [show colour 1=1 from rfl, Lat.touch_one]
   have he: tor (N:=N) (pulseQ f 0)=1 :=by rw [ht]; have hh:rides (Equiv.refl (Site f)) (fun _=> (1:Bundle))=1:=ridden; rw [tor,hh,copies_one]; ext a b; rcases a with a|a <;> rcases b with b|b <;> simp [Matrix.one_apply]
   rw [he]; -- changeVars.one?
   simp
end YM.QCD.Dust
