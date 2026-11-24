import YM.Elms.Sills
/-!
# Independent gauges, root reflections and common representation matching.Park.B
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans MeasureTheory Filter Finset
open scoped Matrix Matrix.Norms.Frobenius InnerProductSpace Topology BigOperators TensorProduct Pointwise Classical ContDiff Stamp Kronecker
open Papyrus.Purl Papyrus LoomC
variable {d:ℕ}
namespace SparK
open Push.Mark YM.Source YM.Source.Drops RG RP
namespace Arbor
open Lining Lining.Temper Poised.Carte.Hem Permit Patria Exposure
variable {n:Side}(U:Grid n)(P : Regulator n 6)
variable (o:Cover)(w v:Walk)(e:Point)(a:Axis)
namespace Gallery
open QCD.Kites PrismD Civic
lemma where_stamp (p:Slot)(i:su.ColorIndex)(v:su.El): whereby v (tendency p i)= ∑ j:su.ColorIndex, (((su.adjoint v (ico j)) i:ℝ) :ℂ) • tendency p j:=by
        -- reuse internal proof S.K
        funext n o; apply ContinuousMap.ext; intro V; simp only [Finset.sum_apply,ContinuousMap.sum_apply]; change transform _ _ V=_; rw [atmosphere]
        let A:=p.eval (expandAt (wrap n o) V); have hx:A=∑ j, A j • ico j:=((EuclideanSpace.basisFun ..).sum_repr A).symm
        have hh: ((su.adjoint v A) i :ℂ) =∑ j, A j • ((↑((su.adjoint v (ico j)) i):ℂ)):=by
           nth_rw 1 [hx]; simp only [map_sum,map_smul]; simp
        change ((↑((su.adjoint v A) i):ℂ)) • (1:Lat.Fields n 6)=_; rw [hh]; rw [sum_smul]; refine Finset.sum_congr rfl fun j _=>?_ ; simp only [Pi.smul_apply, ContinuousMap.smul_apply]; change _= ((↑((su.adjoint v (ico j)) i):ℂ)) • ((↑(A j):ℂ) • (1:Lat.Fields n 6)); rw [Complex.real_smul, mul_comm,← smul_smul]
lemma poolZ (x:Drape)(g t:ℕ)(h:x∈phrase g t): OrbitW x≤ phrase g t:=by
    apply Submodule.span_le.mpr; rintro p ⟨u,rfl⟩; refine Submodule.span_induction (p:=fun y _=>whereby u y∈_) ?_ (by rw [map_zero]; exact Submodule.zero_mem _) (fun x y _ _ h hp=>by rw [map_add]; exact Submodule.add_mem _ h hp) (fun i x _ h=>by rw [map_smul]; exact Submodule.smul_mem _ _ h) h
    rintro z ⟨l,rfl,rfl,rfl⟩
    have he(i:Bough): whereby u (issue i)∈phrase (luminos i) (tallyS i):=by
       cases i with
       | inl i=> change whereby u (tendency i.1 i.2)∈_; rw [where_stamp]; apply Submodule.sum_mem; intro j _; exact Submodule.smul_mem _ _ (miniPage (.inl (i.1,j)))
       | inr j=> change whereby u (burnish j.wal j.q (j.i,j.u))∈_; rw [shake]; apply Submodule.sum_mem; intro i _; exact Submodule.smul_mem _ _ (miniBurn j.q i j.wal) -- error arbitration
    clear h; induction l with
    | nil=> rw [show leaflet []=1 from rfl,show whereby u 1=1 from funext fun n=>funext fun o=> invariant_one (n:=n) (F:=6) (gways u n)]; exact onePage
    | cons a l ih=> rw [show leaflet (a::l)=issue a *leaflet l from rfl,whereby_prod]; exact pages_mul (he a) ih
lemma chapZ {x y:Drape}{g t:ℕ}(h: x∈phrase g t) (he:Shears x y) : y∈phrase g t:=poolZ _ _ _ h (he.in_spin (shelf h).film)
lemma cloak (e:Point)(i:su.ColorIndex): flashF e i∈phrase 1 0:=by
    rw [flashCoins]; apply Submodule.sum_mem; intro p _; unfold hereTerm; split; next _=> apply Submodule.sub_mem; exact miniPage (.inl (_,i)); exact miniPage (.inl (_,i))
    next _=> split
             next _=> apply Submodule.neg_mem; apply Submodule.sub_mem; exact miniPage (.inl (_,i)); exact miniPage (.inl (_,i))
             next _=> exact Submodule.zero_mem _
set_option maxHeartbeats 750000 in
lemma plateBills {I J:Type} [Fintype I][Fintype J] (x:I → Drape) (y:J → Drape) (f:I→ J→ℂ) (g t:ℕ)(hx:∀ i,x i∈phrase g t)(hy:∀ i,y i∈phrase g t): ∑ j:J,∑ i:I,f i j • (x i * y j) ∈ phrase (g+g) (t+t):= Submodule.sum_mem _ (fun j _=> Submodule.sum_mem _ fun i _=> Submodule.smul_mem _ _ (pages_mul (hx i) (hy j)))
lemma glyphF (u v:Walk)(M:ΔM): fuseD u v M∈ phrase 0 2:=plateBills (burnish v false) (burnish u true) (fun i j=> M j i) 0 1 (fun i=> miniBurn false i v) (fun j=>miniBurn true j u)
lemma glowK (e:Point)(i:su.ColorIndex):flashK e (ico i)∈ phrase 0 2:=by rw [postY]; exact Submodule.sub_mem _ (Submodule.neg_mem _ (glyphF _ _ _)) (glyphF _ _ _)
lemma rateSb (w:Walk)(i:Dike)(q:Bool):brake w i q∈ phrase 0 1:=by
   unfold brake; apply Submodule.sum_mem; intro a _; unfold endZ; apply Submodule.sub_mem; exact miniBurn q i w; apply Submodule.add_mem
   all_goals apply Submodule.sum_mem; intro j _; apply Submodule.smul_mem; exact miniBurn q j _ -- ambiguity
-- parity via layer. Pub statements subtree.
lemma grade_phase {A:Type*}[Fintype A](i:ℕ)(x:Alg A)(h:x∈ layer A i): grade x=(-1:ℂ)^i • x:=by
   rw [← write x,map_sum,Finset.smul_sum]; apply Finset.sum_congr rfl; intro j _; by_cases hv:i=j.card; · rw [map_smul,Grass.grade_mono,hv,smul_comm]
   rw [Grass.spectrum h j (Ne.symm hv), zero_smul,map_zero, smul_zero]
noncomputable def polarity (s:ℕ):Bool:= decide (Odd s)
lemma affinity {X:Drape}{g s:ℕ}(h:X∈ phrase g s): moon (polarity s) (X n o):=by
    have hv:=shelf h; have hg:Draft X g s:= whereby_self X ▸ hv.draws 1
    intro V; have h:=grade_phase _ _ (convoy hg V o); by_cases hs: Odd s
    · rw [hs.neg_one_pow,neg_one_smul] at h; rw [show polarity s=true from decide_eq_true hs]; exact h
    have hk:Even s:= Nat.not_odd_iff_even.mp hs
    rw [hk.neg_one_pow,one_smul] at h; rw [show polarity s=false from decide_eq_false hs]; exact h
lemma pol_eq (h i:ℕ):polarity (h+2*i)=polarity h:=by simp [polarity,Nat.odd_iff] -- omega
-- quantity combo
abbrev Profile (x:Drape):Prop:= ∀ n o,Lat.Invariant (x n o)
lemma profileShears (X Y:Drape)(k l:ℕ)(hh:X∈phrase k l)(h: Shears X Y): Profile Y:=h.gauged (shelf hh).film (shelf hh).root
lemma profileVia (x:Drape)(hx:Profile x): Profile (via a x):=fun n o=> routed a _ (hx n _)
-- list operator
noncomputable def evoc (x:Drape): List Axis→Drape | []=> x| a::l=> via a (evoc x l)
lemma spoke {X:Drape}{g t:ℕ}(hx: X∈phrase g t)(l:List Axis):evoc X l∈phrase g t:=by induction l with|nil=> exact hx|cons a y ih=>exact pagesVia a ih
lemma profileEv {x:Drape}(h:Profile x) (l:List Axis):Profile (evoc x l):=by induction l with |nil=>exact h|cons a x ih=> exact profileVia a _ ih
lemma emanated (x y:Drape)(l:List Axis): evoc (x+y) l=evoc x l+evoc y l:=by induction l with|nil=>rfl|cons a l ih=>rw [evoc,ih,map_add]; rfl
lemma layered (x:Drape)(r:ℝ)(l:List Axis): evoc ((r:ℂ) • x) l=(r:ℂ) • evoc x l:=by induction l with |nil=>rfl|cons a l ih=>rw [evoc,ih,map_smulₛₗ, Complex.conj_ofReal]; rfl
lemma coherent {x:Drape}{p:Bool}(h:∀ o:Cover, moon p (x n o))(l:List Axis):∀ o:Cover, moon p (evoc x l n o):=by induction l with |nil=>exact h|cons a l ih=>exact fun o=>moon_mir a (ih _)
lemma stillCap {x:Drape}{p:Bool}{k:ℕ}(hc:P.t=0)(hx:∀ o:Cover, moon p (x n o)) (h:∀ o:Cover, NullOn P (x n o) (Outer k (wrap n o))) (l:List Axis):∀ o:Cover, NullOn P (evoc x l n o) (Outer k (wrap n o)):=by
   induction l with
   | nil=> exact h
   | cons a l ih=> intro o; have hd:= sunny P (axisT a o) a hc (coherent hx l _) (ih _); rw [axis_sq] at hd; exact hd
end Gallery
end Arbor
end SparK
end YM.Massive.Elm
#print axioms YM.Massive.Elm.SparK.Arbor.Gallery.poolZ
