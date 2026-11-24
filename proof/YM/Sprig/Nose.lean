import YM.Sprig.Leaf
/-! Matrix bounds from authenticated probes.C_H independent of Pane; the motion calculus here only for Euclidean deriv. -/
set_option autoImplicit false
noncomputable section
namespace YM.Intag.Sprig
open Function Filter MeasureTheory RG Lattice Wilson Cells
open Massive Massive.Patria Massive.Patria.Hub Massive.Patria.Depth Massive.Patria.Rolls QCD QCD.Tide Tarot QCD.Lat QCD.Grass Massive.Patria.Exposure Massive.Lyre Massive.Lyre.Goblet Massive.Romance
open scoped BigOperators ContDiff Topology Classical TensorProduct Matrix.Norms.L2Operator ComplexOrder Interval
variable {C:Sequence} {D d d' n:ℕ} (P:Calibration C)
open YM.Eden Tarot.Vista CardsT QCD.Acre.Stratum.MarchQ QCD.Acre.Stratum.MarchQ.Suburb QCD.Acre.Stratum.MarchQ.Suburb.Talis QCD.Acre.Stratum.MarchQ.Suburb.Talis.Grammar Sapphire MintV
open Poised Display Plans Sieve Plans.Stamp SourceRead Canvas Ibis QCD.Plum Massive.Elm.SparK.Arbor.Gallery
open UV Vale Massive.Needle Massive.Tarn Massive.Fir YM.Fir.NoteF
namespace Compass
variable (A:Compass C D)
variable (φ:ℕ→ℕ)(V:∀ d,Label d→ₗ[ℂ] Label d)(Q:Massive.Tarn.Choir)(hQ:Q.Harmony P φ)
variable (K:DiscP P A φ V Q) (L:Vale.Laurel d)(J:Vale.Landing P.sym L) (B:Inn P A J)
variable (u:Q.W)(p:Fin n)(x:Points n)(a:Axis)
open Function Set Finset Metric

local notation "Yy"=>scout P L J a
local notation "l"=> (J.l/2)
local notation "VZ"=>Stokes d
local notation "W"=>oppositeX P V Q L
local notation "ΓW"=> harp V Q L
local notation "σ"=> saver P A V Q L J u a
include hQ K B
lemma ansatz (t:VZ →ℂ)(j:Stokes d): Γ (moonGate P A V Q L J a) t j=((J.l/2)^(-1:ℤ):ℝ) • ∫ s:ℝ in 0..(J.l/2),saver P A V Q L J (harp V Q L t) a j s:=by
     simp_rw [saver, ← stringed P A V Q L]; let F(k: Stokes d)(s):= curveP P A V Q L (scout P L J a s) j k; simp only[zpow_neg, zpow_one, ne_eq,Int.reduceNeg] -- r inv^-
     change ∑ k,(l⁻¹ • (∫ s:ℝ in 0..l,F k s))*(t k)=l⁻¹ • (∫ s:ℝ in 0..l,∑ k,F k s*t k)
     rw [intervalIntegral.integral_finsetSum (f:=fun i s=>F i s*t i) (fun i _=> (iturn P A φ V Q hQ K L J B a j i).mul_const (t i)),Finset.smul_sum]; simp only [smul_mul_assoc,intervalIntegral.integral_mul_const]
lemma dirE (Y : Q.W)(i:Stokes d) : ∫ s:ℝ in 0..(J.l/2), tap A Q (oppositeX P V Q L i) ((scout P L J a) s) (bright Q A.r a Y)= glimpseT A Q (W i) Y (scout P L J a l)-glimpseT A Q (W i) Y (scout P L J a 0):= by
      have h := integrated P A φ V Q hQ K L J B (bright Q A.r a Y) a i; simp_rw[pours] at h ⊢; exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht=> skyArc P A φ V Q hQ K L J B Y a t ht) h
variable (x':Text d')(hD:d'+2=d)
-- native Wick expected pair.Any unequal.Tone economic.L.Measuring derivative arbitrary symbol of chart only. Arc d' to d. Values depend only P.sym and chart.L.
omit hQ K B
noncomputable def fixedP (i:Stokes d)(a:Axis)(s:ℝ):ℂ:= candle (![ GlyphV (opposite P.sym timeAxis (L.F i)) (max d d') (le_max_left ..), GlyphV x' _ (le_max_right ..)]) (![0,scout P L J a s])
noncomputable def wealth (i:Stokes d)(a:Axis):= ‖fixedP P L J x' i a l‖+‖fixedP P L J x' i a 0‖+J.ε
lemma gilded(i:Stokes d) : 0≤ wealth P L J x' i a:=by unfold wealth; linarith only[J.light,norm_nonneg (fixedP P L J x' i a l),norm_nonneg (fixedP P L J x' i a 0)]
-- parameter bound
include hQ K B
variable (hD':d' ≤ D)(hf:GlyphV x' D hD' ∈ A.Ω)(he:x'.mark≠0)
local notation "WU"=> (GlyphV x' _ hD')
local notation "Zf"=> choiceT V Q x'.mark
include hD hf he
lemma north (i:Stokes d)(t:ℝ)(ht:t∈ Set.uIcc 0 (J.l/2)): ‖tap A Q (oppositeX P V Q L i) (scout P L J a t) (choiceT V Q x'.mark)-fixedP P L J x' i a t‖ ≤ J.ε/4:=by
     let X := (![ GlyphV (opposite P.sym timeAxis (L.F i)) D B.level, GlyphV x' D hD'] : Fin 2 → Glyph D); let u:=scout P L J a t
     have ht'(i':Fin 2):X i'∈A.Ω:=by fin_cases i'; exact (B.rich i).2 ; exact hf
     have he'(i':Fin 2): (X i').material≠0:=by fin_cases i'; exact fun h=> Vale.living L i ((P.sym.adj _ timeAxis).injective (h.trans (map_zero _).symm)); exact he
     have hh:= (K.homes X ht' he' d L J B.suit B.vast u (rocks P L J a t ht)).trans B.poise
     let m(i':Fin 2):=GlyphV (opposite P.sym timeAxis (L.F i)) (max d d') (le_max_left ..)
     let v' : Fin 2 →Glyph (max d d'):= ![m 0,GlyphV x' _ (le_max_right ..)]; have hi:menuP v'=menuP X:=funext fun i=>by fin_cases i<;>rfl
     have h1:fixedP P L J x' i a t= candle X (![0,u]):=by
          change UV.Free.wick (menuP v') _ (fun i=> (v' i).material) = UV.Free.wick (menuP X) _ (fun i=>(X i).material)
          suffices hx:∀ (x:Fin 2→ℕ)(w: (i:Fin 2)→Label (x i)),x=menuP X→ HEq w (fun i=>(X i).material) → UV.Free.wick x (points (![0,u])) w= UV.Free.wick (menuP X) (points (![0,u])) (fun i=>(X i).material) by
               refine hx (menuP v') _ hi (Function.hfunext rfl ?_)
               intro i j h; have he:i=j:=eq_of_heq h; subst i; fin_cases j<;>rfl
          intro x w h hP; subst x; suffices e:w=(fun i=>(X i).material) by rw[e]
          exact eq_of_heq hP

     rw[pours]; suffices h:(glimpseT A Q (W i) (choiceT V Q x'.mark) u)= learned A V Q X ![0,u] by rw [show glimpseT _ _ _ _ _ =_ from h,h1]; exact hh
     apply congr_arg (Q.total 2 _); funext j; fin_cases j<;>rfl
omit hD hf he
noncomputable def forge(u: ↥(Q.level d)) : Stokes d →ℂ:= (coil P A φ V Q hQ K L J B).symm u
lemma roars (U: Q.W)(hm:U∈ Q.level d)(y: Stokes d→ℂ)(h: y= forge P A φ V Q hQ K L J B ⟨U,hm⟩) : U=∑ i:Stokes d,y i • fieldS V Q L i:=by
     subst y; let Vq:= coil P A φ V Q hQ K L J B; let u:↥(Q.level d):=⟨U,hm⟩; exact congr_arg Subtype.val (Vq.apply_symm_apply u).symm
noncomputable def money := J.J*((J.l/2)⁻¹*(∑ j:Stokes d,wealth P L J x' j a))
lemma rooft : 0 ≤ money P L J a x':=mul_nonneg J.fee (mul_nonneg (inv_nonneg.mpr (half_pos J.breadth).le) (Finset.sum_nonneg fun j _=>gilded P L J a x' j))
include hD hf he
lemma rake (hx:bright Q A.r a (choiceT V Q x'.mark)∈ Q.level d)(βt:Stokes d→ℂ)(hv : βt=forge P A φ V Q hQ K L J B ⟨_,hx⟩): ‖βt‖ ≤ money P L J a x':=by
      let u:= bright Q A.r a (choiceT V Q x'.mark); let U: ↥(Q.level d):= ⟨u,hx⟩; let m:= moonGate P A V Q L J a; let f:= Γ m βt; apply le_trans (J.warmth (glowing P A φ V Q hQ K L J B a) βt)
      let X(j:Stokes d):=wealth P L J x' j a; change J.J * ‖f‖ ≤ J.J*(l⁻¹ * ∑ j,X j); apply mul_le_mul_of_nonneg_left _ J.fee
      have ht:0<l:= half_pos J.breadth; refine (pi_norm_le_iff_of_nonneg (mul_nonneg (inv_nonneg.mpr ht.le) (sum_nonneg fun i _=>gilded P L J a x' i))).mpr fun i=>?_
      let g(t):= glimpseT A Q (W i) (choiceT V Q x'.mark) ((scout P L J a) t)
      have heq:(coil P A φ V Q hQ K L J B) βt=U:=by rw[hv]; exact LinearEquiv.apply_symm_apply _ _
      have h1:f i= l⁻¹ • (g l-g 0):=by
           have hh:= ansatz P A φ V Q hQ K L J B a βt i; rw [show harp V Q L βt =U from heq] at hh; change f i = (l^(-1:ℤ):ℝ) • _ at hh; rw [zpow_neg,zpow_one] at hh; apply hh.trans; apply congr_arg ((l⁻¹) • ·); exact dirE P A φ V Q hQ K L J B a (choiceT V Q x'.mark) i
      rw[h1,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr ht.le)]; apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ht.le)
      have hp(s:ℝ)(hs:s∈Set.uIcc 0 l) : ‖g s‖ ≤ ‖fixedP P L J x' i a s‖+J.ε/4 :=by
               have h:=north P A φ V Q hQ K L J B a x' hD hD' hf he i s hs; rw[pours] at h; exact sub_le_iff_le_add'.mp ((norm_sub_norm_le (g s) _).trans h)
      apply (norm_sub_le ..).trans; apply le_trans _ (single_le_sum (fun i' _=> (gilded P L J a x' i')) (mem_univ i)); change _ ≤ X i; unfold X wealth; linarith only [hp l (Set.right_mem_uIcc),hp 0 (Set.left_mem_uIcc),J.light]
lemma expenses:∃ y:Stokes d→ℂ, ‖y‖ ≤ money P L J a x' ∧ bright Q A.r a (choiceT V Q x'.mark)=∑ i:Stokes d,y i • fieldS V Q L i :=by
     have hp:bright Q A.r a (choiceT V Q x'.mark)∈ Q.level d:= by rw [←hD]; exact (Q.level _).smul_mem _ (hQ.h.graded a d' _ (⟨_,rfl⟩: choiceT V Q x'.mark∈Q.level d'))
     let u:↥(Q.level d):=⟨_,hp⟩; exact ⟨forge P A φ V Q hQ K L J B u,rake P A φ V Q hQ K L J B a x' hD hD' hf he hp _ rfl, roars P A φ V Q hQ K L J B _ _ _ rfl⟩
end Compass
end YM.Intag.Sprig
#print axioms YM.Intag.Sprig.Compass.expenses
