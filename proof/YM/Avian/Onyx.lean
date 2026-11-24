import YM.Avian.Stroll
import YM.Plateau.Snow
import YM.Sprig.Echoes
/-! Off-Shell Families via aligned signs. Chooses orthogonal splittings globally not T-specific.M.Across orientations. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Patria.Gall
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix Matrix.Norms.L2Operator TensorProduct Classical InnerProductSpace
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Oriole Poised Poised.Beacon Kit Push.Local
open QCD.Revolve TorusPCAC.Geometry Lining Lining.Ferry Lining.Temper Canvas PCAC QCD.Entr.Goals
open Tawny Tawny.Cast Tawny.Cast.TableT Tawny.Cast.Rays Perla Fore Perla.BrickM Zinc Carnal
open Pane BendR UV.Free KeysP Clifford
open YM.Sprig Tarn Tarn.Choir Pollens
variable {C:Sequence}{P:Calibration C}{φ:ℕ→ℕ}{Q:Choir}{d m:ℕ}(T:Pollens P Q)
namespace Onyx
variable {I:Type}[Fintype I]
structure Nest(I:Type) where
    Q: Signed → Equiv.Perm I
    c: Signed → I→ℝ
    w(s i): c s i*c s i=1
    t:Equiv.Perm I
    e:ℂ
variable (J:Nest I)(i:I)
noncomputable abbrev Plain(i:Nest I)(d:ℕ):Submodule ℂ (I→Label d):= Steno (fun s x=> i.Q s x) i.c i.t i.e d
local notation "A"=> Plain J d


-- orthogonal frame every coordinate cal root
abbrev BrushQ:= {p:EuPin×Signed//p.1.Lifts p.2}
abbrev Axe:= FlavorTorus ⊕ (BrushQ ⊕ Fin 3) -- f,p,parity,charge,slot/swap
section algebra
variable {X:Type*} [AddCommGroup X] [Module ℂ X]
private noncomputable def rises (G: X ≃ₗ[ℂ] X)(s:Signed): (I→X) ≃ₗ[ℂ](I→X):={
   toFun x i:= (J.c s ((J.Q s).symm i):ℂ) • G (x ((J.Q s).symm i))
   invFun x i:= (J.c s i:ℂ) • G.symm (x (J.Q s i))
   left_inv x:=funext fun i=>by simp only[Equiv.symm_apply_apply,map_smul,LinearEquiv.symm_apply_apply,smul_smul,←Complex.ofReal_mul,J.w,Complex.ofReal_one,one_smul]
   right_inv x:=funext fun i=>by simp only[Equiv.apply_symm_apply,map_smul,LinearEquiv.apply_symm_apply,smul_smul,←Complex.ofReal_mul,J.w,Complex.ofReal_one,one_smul]
   map_add' x y:=funext fun i=>by simp only [Pi.add_apply,map_add,smul_add]
   map_smul' q y:=funext fun i=>by simp only [Pi.smul_apply,map_smul,RingHom.id_apply]; exact smul_comm .. }
omit [Fintype I] in
noncomputable abbrev rung (G:X≃ₗ[ℂ]X): (I→X)≃ₗ[ℂ](I→X):= LinearEquiv.piCongrRight (fun _=>G)
noncomputable def sway (Q:Equiv.Perm I) : (I→X)≃ₗ[ℂ](I→X):={
    toFun x:=x ∘ Q,invFun x:=x ∘ Q.symm, left_inv x:=funext fun i=>by simp
    right_inv x:=funext fun i=>by simp
    map_add' x y:=rfl
    map_smul' q y:=rfl }
noncomputable def animals (f:FlavorTorus → X≃ₗ[ℂ]X)(g:EuPin → X ≃ₗ[ℂ] X)(p c:X≃ₗ[ℂ] X) (s:Axe): (I→X)≃ₗ[ℂ](I→X) := Sum.elim (fun i=> rung (f i)) (Sum.elim (fun i=> rises J (g i.val.1) i.val.2) (![rung p,rung c,sway J.t])) s
end algebra
noncomputable def roar(sym:RawSym) (d:ℕ):Axe→(I→Label d)≃ₗ[ℂ](I→ Label d):= (animals (X:=Label d) J (sym.flavor d) (sym.pin d) (sym.parity d) (sym.charge d))
noncomputable def lion : Axe→(I→Q.W) ≃ₗ[ℂ] (I→Q.W):= animals J T.flavor T.spin T.parity T.charge
noncomputable def calls : Axe→ℂ:= Sum.elim (fun _=>1) (Sum.elim (fun _=>1) (![1,1,J.e]))
variable (d)
private lemma alignP (sym:RawSym)(v:I→Label d) : v∈Plain J d ↔ ∀ i, roar J sym d i v=calls J i • v:=by
    constructor
    · intro h i; change Meaning _ _ _ _ d v at h; funext a; rcases i with u|h0
      · change sym.flavor d u _ = (1:ℂ) • v a; rw [one_smul]; apply Subtype.ext; rw[sym.flavorActs]; exact (h.light a).2 u
      rcases h0 with ⟨⟨p,s⟩,hp⟩|j
      · obtain ⟨z,rfl⟩:= (J.Q s).surjective a; change (J.c s ((J.Q s).symm _) :ℂ) • sym.pin d p (v ((J.Q s).symm _)) = (1:ℂ) • v _; rw[Equiv.symm_apply_apply, one_smul]; apply Subtype.ext; rw [Submodule.coe_smul,sym.pinActs,h.ringo _ _ hp]; change (↑(J.c s z):ℂ) • (↑(J.c s z):ℂ) • _ =_; rw[smul_smul,←Complex.ofReal_mul, J.w,Complex.ofReal_one,one_smul]
      fin_cases j
      · change sym.parity d _= (1:ℂ) • _; rw[one_smul]; exact Subtype.ext ((sym.parityActs ..).trans (h.light _).1)
      · change sym.charge d _= (1:ℂ) • _; rw[one_smul]; exact Subtype.ext ((sym.chargeActs ..).trans (h.coal _))
      exact h.sym _
    intro h; refine ⟨fun a=>⟨?_,fun u=>?_⟩,fun a=>?_,fun s w hp a=>?_,fun a=>?_⟩
    · rw [←sym.parityActs]; have ht:sym.parity _ (v a)=(1:ℂ) • _:=congr_fun (h (.inr (.inr 0))) a; rw[ht,one_smul]
    · rw[←sym.flavorActs]; have ht:sym.flavor _ u (v a)=(1:ℂ) • _:=congr_fun (h (.inl u)) a; rw[ht,one_smul]
    · rw [←sym.chargeActs]; have ht:sym.charge _ (v a)=(1:ℂ) • _:=congr_fun (h (.inr (.inr 1))) a; rw[ht,one_smul]
    · have ht:=congr_fun (h (.inr (.inl ⟨(w,s),hp⟩))) (J.Q s a); rw [←sym.pinActs]; change (J.c s ((J.Q s).symm _) :ℂ) • sym.pin d w (v ((J.Q s).symm _)) = (1:ℂ) • v _ at ht; rw [Equiv.symm_apply_apply,one_smul] at ht; change _= _ • ((v (J.Q s a)).val); rw [← ht,Submodule.coe_smul, smul_smul,← Complex.ofReal_mul,J.w,Complex.ofReal_one,one_smul]
    exact congr_fun (h (.inr (.inr 2))) a
variable {C:Sequence}{P:Calibration C}(n:Side)(hp:P.System)(he:Injective (P.candidate d n 0)) -- WARNING shadow
include hp he
private lemma template :∃ e:InnerProductSpace.Core ℂ (I→Label d),∀ (x y:I→Label d) i,e.inner (roar J P.sym _ i x) (roar J P.sym _ i y)=e.inner x y:=by
    let V(x y:I→Label d):= ∑ i: I,Chloe.pollen P n (x i) (y i)
    let v:InnerProductSpace.Core ℂ (I→ Label d):={
        inner:=V, conj_inner_symm x y:=by unfold V; rw [map_sum]; exact sum_congr rfl fun i _=> Chloe.sparks .. -- orientation
        re_inner_nonneg x:=by change (0:ℝ)≤ (V x x).re; unfold V; rw [Complex.re_sum]; exact sum_nonneg fun i _=> Chloe.pp0 ..
        add_left x y z:=by unfold V; simp_rw [Pi.add_apply,Chloe.timely,sum_add_distrib]
        smul_left x y r :=by unfold V; simp_rw [Pi.smul_apply,Chloe.money,Finset.mul_sum]; rfl
        definite x h:=funext fun i=> by
           by_contra hx; have hP:0 < (V x x).re:=by unfold V; rw [Complex.re_sum]; apply (Chloe.ppU P n _ he hx).trans_le; exact single_le_sum (fun i _=> Chloe.pp0 ..) (mem_univ i)
           rw [show V x x=0 from h, Complex.zero_re] at hP; exact (lt_irrefl _ hP) }
    refine ⟨v,fun x y i=>?_⟩; change V _ _ = _; rcases i with u|j
    · exact sum_congr rfl fun i _=> Chloe.fauna P n _ _ hp u
    rcases j with ⟨⟨p,s⟩,h⟩|i
    · unfold V; rw [← Equiv.sum_comp (J.Q s)]; refine sum_congr rfl fun i _=>?_ ; let j:= J.Q s; let g:=rises J (X:=Label d) (P.sym.pin d p) s; let a:ℂ:= J.c s i; change Chloe.pollen P n (g x (j i)) (g y (j i))=_; have hg(x:I→Label d) : g x (j i)=a • P.sym.pin d p (x i):=by unfold g rises; change (J.c s (j.symm _) :ℂ) • P.sym.pin d p (x (j.symm _))=_; rw [j.symm_apply_apply]; --
      rw[hg,hg,Chloe.money]; rw[← Chloe.sparks P n _ (_:Label d),Chloe.money]; unfold a; rw [star_mul', star_star, show star ((_ :ℝ):ℂ)=_ from Complex.conj_ofReal _,← mul_assoc, ← Complex.ofReal_mul,J.w,Complex.ofReal_one,one_mul,Chloe.sparks, Chloe.brood P n _ _ hp p s h] -- debug
    fin_cases i
    · exact sum_congr rfl fun i _=> Chloe.parityE P n _ _ hp
    · exact sum_congr rfl fun i _=> Chloe.gloss P n _ _ hp
    exact Equiv.sum_comp J.t (fun i:I=>Chloe.pollen P n (x i) (y i))

omit hp he
private lemma unified (x y:RawSym)(d:ℕ): roar J x d = roar J y d:=by
    have h1: x.parity d=y.parity d:= LinearEquiv.ext fun a=> Subtype.ext ((x.parityActs ..).trans (y.parityActs ..).symm)
    have h2: x.charge d=y.charge d:= LinearEquiv.ext fun a=> Subtype.ext ((x.chargeActs ..).trans (y.chargeActs ..).symm)
    have hf: x.flavor d=y.flavor d:= funext fun t=> LinearEquiv.ext fun a=> Subtype.ext ((x.flavorActs ..).trans (y.flavorActs ..).symm)
    have hp: x.pin d=y.pin d:=funext fun t=> LinearEquiv.ext fun a=> Subtype.ext ((x.pinActs ..).trans (y.pinActs ..).symm)
    unfold roar; rw[h1,h2,hf,hp]
open Submodule
structure Tackle (P:(I→Label d)→ₗ[ℂ](I→Label d)):Prop where
     root x : P x∈ Plain J d
     same x: x∈ Plain J d→ P x=x
     pays (U:Submodule ℂ (I→Label d))(s:RawSym)(h:∀ x i,x∈U ↔ roar J s d i x∈U): (∀ x∈U,P x∈U)∧(∀ x,(∀ i,roar J s d i x-(calls J i) • x∈ U)→ x-P x∈U)
include hp he
lemma paddle :∃ P:(I→Label d)→ₗ[ℂ](I→Label d),Tackle d J P:=by
    obtain ⟨e,hE⟩:=template d J n hp he
    obtain ⟨Z,hZ,hP,hV⟩:= YM.Sprig.ports e (roar J P.sym d) (calls J) (Plain J d) (alignP d J P.sym) hE; refine ⟨Z,hZ,hP,fun U s hs=>?_⟩; rw[unified J s P.sym] at hs; rw [unified J s P.sym]; exact hV _ hs
omit hp he
section taxa
variable {X Y:Type}[AddCommGroup X][Module ℂ X][AddCommGroup Y][Module ℂ Y]
structure PulseT (d:ℕ) (V: I→Label d→ₗ[ℂ]Y)(W:Axe→(I→Y)≃ₗ[ℂ](I→Y))(sym:RawSym):Prop where
   spin (i:Axe)(x:I→Label d)(j:I) : V j (roar J sym d i x j) = W i (fun i=> V i (x i)) j
variable (V:I→Label d →ₗ[ℂ] Y)(W:Axe→(I→Y)≃ₗ[ℂ](I→Y))
noncomputable def twix (V:I→Label d→ₗ[ℂ]Y):(I→Label d)→ₗ[ℂ](I→Y):= LinearMap.pi fun i=> V i ∘ₗ LinearMap.proj i
noncomputable def grab (V:I→Label d→ₗ[ℂ]Y):Plain J d→ₗ[ℂ](I→Y):= twix d V ∘ₗ (Plain J d).subtype
lemma portrait {V:I→Label d→ₗ[ℂ]Y}{W: Axe→(I→Y)≃ₗ[ℂ](I→Y)}{s:RawSym}(h:PulseT J d V W s)(t:(I→Label d)→ₗ[ℂ](I→Label d))(ht:Tackle d J t)(f:I→Y): f∈(grab d J V).range↔ (∀ i,W i f=calls J i • f) ∧ ∀ i,f i∈(V i).range:=by
     constructor
     · rintro ⟨u,rfl⟩; refine ⟨fun i=> ?_,fun i=> ⟨_,rfl⟩⟩; have he:= (alignP d J s _).mp u.property i; funext j; let z:= calls J i; change W i (fun i=> V i (u.val i)) j = z • V j (u.val j); rw [show W i _ j= _ from (h.spin i u j).symm,he]; exact map_smul (V j) z (u.val j)
     rintro ⟨h1,H⟩; choose F hF using H; let Ω:=twix d V; have hV: Ω F=f:= funext hF; have hm(i:Axe)(x:I→Label d):Ω (roar J s d i x)= W i (Ω x):= funext fun j=> h.spin ..
     let U:=Ω.ker; have hx:= ht.pays U s (fun x i=>by change Ω x=0 ↔ Ω _=0; rw [hm]; exact ⟨fun hx=>by rw[hx,map_zero],fun hy=> (W i).injective (hy.trans (map_zero _).symm)⟩)
     have he:Ω F-Ω (t F)=0:=by rw [←map_sub]; refine hx.2 F (fun i=> ?_); change Ω _=0; exact (map_sub Ω ((roar J s d i) F) ((calls J i) • F)).trans (by rw[hm,map_smul,hV,h1,sub_self]) -- instance
     exact ⟨⟨t F,ht.root _⟩,(sub_eq_zero.mp he).symm.trans hV⟩
end taxa
end Onyx
end YM.Massive.Patria.Gall
#print axioms YM.Massive.Patria.Gall.Onyx.alignP
