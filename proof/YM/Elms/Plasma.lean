import YM.Elms.Niche
/-! # Grassmann IBP with disjoint stencil. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans MeasureTheory Filter Finset
open scoped Matrix Matrix.Norms.Frobenius InnerProductSpace Topology BigOperators TensorProduct Pointwise Classical ContDiff Stamp Kronecker
open Papyrus.Purl Papyrus LoomC
variable {d:ℕ}
namespace SparK
open LinearMap
open Push.Mark YM.Source YM.Source.Drops RG RP
namespace Arbor
variable {n:Side}(U:Grid n)(P : Regulator n 6)
variable (o:Cover)(w v:Walk)(e:Point)(a:Axis)
local notation "M" => Mat
local notation "N" => Lat.Fields n 6
local notation "K" g:arg=>landsE n o g
local notation "T" g:arg=>stripe n o g U
noncomputable def solar (q:Bool)(o:Cover)(w:Walk)(i:Dike): Insertion n 6:= ((P.m i.2:ℂ)) • cane n q o w i + ∑ a:Axis,(cane n q o w i - ((∑ j:Dike, revM q (mL (Lat.lo a)) i j • cane n q o (adWalk q w a) j)+(∑ j:Dike, revM q (mL (hi a)) i j • cane n q o (adWalk (!q) w a) j)))
lemma solar_up(q:Bool)(i:Dike): solar P q o w i U= windR P q o w U i:=by
    unfold solar; simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply,ContinuousMap.sum_apply, ContinuousMap.sub_apply]; rfl
section
variable {A:Type*}[Fintype A]
lemma leftD (i:A)(L: Matrix A A ℂ) : vary (Sum.inl i) (Grass.form L)=∑ u:A,L u i • Grass.bar u:=by
   unfold Grass.form; simp only [map_sum,map_smul]; have he (u j:A): vary (Sum.inl i) (Grass.psi j * Grass.bar u)= if j=i then Grass.bar u else 0:=by
      rw [vary_head, show vary (Sum.inl i) (Grass.bar u)=0 from vary_off _ _ Sum.inl_ne_inr]; by_cases h:j=i; · subst i; simp [probe]
      simp [probe,h,Ne.symm h]
   apply sum_congr rfl; intro u _; rw [sum_eq_single i]; · simp_rw [he, if_true]
   · intro j _ hj; rw [he,if_neg hj,smul_zero]
   simp
lemma leftPay (i:A)(L: Matrix A A ℂ) (x:Dirac A): ber A (gauss L *((∑ u:A,L u i • Grass.bar u)*x))= -ber A (gauss L*vary (.inl i) x):= by
      have ht:= integration (gauss L*x) (.inl i); rw [vary_mul,show grade (gauss L)= gauss L from gauss_plus _,gauss,varies_exp _ _ (form_plus _),leftD,mul_assoc,map_add] at ht; exact eq_neg_of_add_eq_zero_left ht
end
def thetaL (q:Bool)(i:Dike)(y:Site n): Pairs (Modes n 6):=if q then Sum.inl (place y i) else Sum.inr (place y i)
def Omitted (x:Site n)(Y:Insertion n 6):Prop:= ∀ z:Dike,∀ q:Bool,∀ U, vary (thetaL q z x) (Y U) =0
lemma bare_force (h:P.t=0)(i:Dike)(q:Bool)(Y:Insertion n 6)(he: Omitted (K w) Y): P.average (solar P q o w i*Y)=0:=by
   suffices hv:P.raw (solar P q o w i*Y)=0 by simp [Regulator.average,hv]
   have hg (U:Grid n): ber _ (P.density U * (solar P q o w i U * Y U))=0:=by
       rw [solar_up, ← star_bill U P o w h q i, Regulator.density_apply,sum_mul]; rw [_root_.smul_mul_assoc,mul_sum,map_smul,map_sum,sum_eq_zero,smul_zero]
       intro v _; rw [_root_.smul_mul_assoc,_root_.mul_smul_comm,map_smul]; cases q
       · change _ • ber _ (gauss (P.D U)*((∑ j:Modes n 6,P.D U (place (K w) v) j • psi j)*Y U))=0; rw [Grass.answer,show vary (.inr (place (K w) v)) (Y U) = 0 from he v false U,mul_zero,map_zero,smul_zero]
       change _ • ber _ (gauss (P.D U)*((∑ j:Modes n 6,P.D U j (place (K w) v) • bar j)*Y U))=0; rw [leftPay,show vary (.inl (place (K w) v)) (Y U) = 0 from he v true U,mul_zero,map_zero,neg_zero,smul_zero]
   change (∫ U:Grid n, ber _ (P.density U*(solar P q o w i U *Y U)) ∂prior su n)=_; simp_rw [hg]; exact integral_zero ..
-- disjoint support.P extra.Follows floors.
lemma staysL (x:Insertion n 6)(y:Site n)(S:Set (Site n))(hf:y∉S)(hQ:RP.Floors S x):Omitted y x:=by
    intro z q U; obtain ⟨s,hS,hS',h⟩:=hQ; rw [h];
    have ht(a:RP.Deck S 6): y ≠ (setDay S a).1.1:= fun h=> hf (h.symm ▸ a.1.1.property)
    have hv(i: Pairs (RP.Deck S 6)): vary (thetaL q z y) (pass (setDay S) (Grass.atom i))=0:=by
        cases i with
        | inl a=> rw [show pass _ _= _ from pass_psi (setDay S) a]; exact Grass.vary_off _ _ (by intro h; cases q; exact Sum.inr_ne_inl h; exact ht _ (congr_arg (Prod.fst ∘ Prod.fst) (Sum.inl.inj h)))
        | inr a=> rw [show pass _ _=_ from pass_bar (setDay S) a]; exact Grass.vary_off _ _ (by intro h; cases q; exact ht _ (congr_arg (Prod.fst ∘ Prod.fst) (Sum.inr.inj h)); exact Sum.inl_ne_inr h)
    have hh(l:List (Pairs (RP.Deck S 6))): vary (thetaL q z y) (pass (setDay S) (l.map Grass.atom).prod)=0:=by
         induction l with
         | nil=>simp [vary_one]
         | cons a l ih=> simp only [List.map_cons,List.prod_cons,map_mul,vary_mul,ih,hv,zero_mul,mul_zero,add_zero]
    rw [← write (s U)]; simp only [map_sum,map_smul]; refine sum_eq_zero fun i _=>?_ ; obtain ⟨b,-,-,hp⟩:=expression i; rw [hp]; erw [show vary (thetaL q z y) (pass (setDay (F:=6) S) (List.ofFn (atom ∘ b)).prod) = 0 from ?_, smul_zero]; simpa only [List.map_ofFn] using hh (List.ofFn b) -- avoid hp coefficient change.N
lemma Omitted.joins {x y:Insertion n 6}{p:Site n}(hp:Omitted p x)(hq:Omitted p y): Omitted p (x*y):=by intro z q U; rw [ContinuousMap.mul_apply,vary_mul,hp,hq,zero_mul,mul_zero,zero_add]
end Arbor
end SparK
end YM.Massive.Elm
