import YM.Elms.Sprite
/-!
# Lists of qualified generator multipliers. Unrestricted products (engineering
 cap paid at end) in THESE formula assertions. Gauging taken at
 root, avoidance includes AP lifts later. Reflection no polynomial side input.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans MeasureTheory Filter
open scoped Topology BigOperators TensorProduct Pointwise Classical ContDiff Stamp
open Papyrus.Purl Papyrus LoomC
variable {d:ℕ}
namespace SparK
open LinearMap
variable (R: Submodule ℂ (Label d))
open Push.Mark YM.Source YM.Source.Drops RG
variable (H:Hol su)(hp:∀ k,Peg H k)
structure Barge where
   -- sample path can always be arbitrary length
   wal : Walk
   q : Bool
   i : Fiber
   u : Flavor 6
noncomputable abbrev Bough := Sum (Slot × su.ColorIndex) Barge
def Barge.pos (b:Barge): Cover:= stop 0 b.wal
def carat (v:Bough)(e:Edge Cover) : Prop:=Sum.elim (fun p=> safe e p.1) (fun j=> avoids 0 j.wal e) v
def vacant (v:Bough)(b:Cover): Prop:=Sum.elim (fun _=>True) (fun j=> j.pos≠b) v
def permitted (v:Bough)(e:Edge Cover)(b:Cover): Prop:=carat v e∧vacant v b -- stronger enough? gauge slots no fail spin. spin supports paths yes
noncomputable def climber (d:ℕ)(v:Bough): Pol d:= Sum.elim (fun p=> coarse d (spell (d/2) (safeLinear H (d/2) p.1 p.2))) (fun j=> flora (Grass.line (twig j.q j.i j.u (vector j.pos)))) v
noncomputable def canopy (d:ℕ)(l:List Bough):Pol d:= (l.map (climber H d)).prod
lemma canopy_more (d:ℕ)(l:List Bough)(x:Bough): canopy H d (x::l)=climber H d x * canopy H d l:=by simp [canopy]
lemma canopy_join (d:ℕ)(l q: List Bough): canopy H d (l++q)=canopy H d l*canopy H d q:=by simp [canopy]
noncomputable def Pavilion (e:Edge Cover)(b:Cover)(d:ℕ): Submodule ℂ (Mini d):= Submodule.span ℂ {x| ∃ l:List Bough,(∀ p∈l,permitted p e b) ∧ setas d (canopy H d l)=x}
section Arbitrary
variable (e:Edge Cover)(b:Cover)
local notation "O"=>Pavilion H e b d
lemma pavilion_mul (x y:Pol d) (hx:setas d x∈O)(hy:setas d y∈O) : setas d (x*y)∈O:=by
   have he(u v:Pol d): setas d (u*v)=setas d ((setas d u).val*(setas d v).val):=by apply Subtype.ext; change drips d _=drips d (_*_); exact ((mulDry_left d d u (drips d v)).trans (mulDry_right d d u v)).symm
   rw [he]; refine Submodule.span_induction (p:=fun u _=> setas d (u.val*(setas d y).val)∈O) ?_ (by simp) (fun x z _ _ hx hy=>by rw [Submodule.coe_add,add_mul,map_add]; exact (Pavilion H e b d).add_mem hx hy) (fun c u _ hh=>by rw [Submodule.coe_smul_of_tower,_root_.smul_mul_assoc,map_smul]; exact (Pavilion H e b d).smul_mem _ hh) hx
   rintro _ ⟨u,hu,rfl⟩; let U:=setas d (canopy H d u)
   refine Submodule.span_induction (p:=fun v _=> setas d (U.val*v.val)∈O) ?_ (by simp) (fun v w _ _ hv hw=> by rw [Submodule.coe_add,mul_add,map_add]; exact (Pavilion H e b d).add_mem hv hw) (fun c v _ hv=>by rw [Submodule.coe_smul_of_tower,_root_.mul_smul_comm,map_smul]; exact (Pavilion H e b d).smul_mem _ hv) hy
   rintro _ ⟨v,hv,rfl⟩; exact Submodule.subset_span ⟨u++v,(fun i hi=> (List.mem_append.mp hi).elim (hu i) (hv i)),by rw [canopy_join]; exact he _ _⟩
lemma pavilion_one : setas d (1:Pol d)∈O:=Submodule.subset_span ⟨[],by simp,rfl⟩
lemma buds (p:Bough)(hh:permitted p e b): setas d (climber H d p)∈ O:=Submodule.subset_span ⟨[p],fun i hi=> (List.mem_singleton.mp hi).symm ▸ hh,(by simp [canopy])⟩
lemma heights (l:Letters d):setas d (flora (Grass.atom l))∈ O:=by
   obtain ⟨q,w,hw⟩:∃ (q:Bool)(w:SpinMode d),Pulses.leafD q w.1.2.1 w.1.2.2 w.2 w.1.1=l:=by cases l; exact ⟨false,_,rfl⟩; exact ⟨true,_,rfl⟩ -- metavars
   obtain ⟨⟨p,i,k⟩,u⟩:=w; obtain ⟨F,hF⟩:=floraL (d:=d); let L:= setas d ∘ₗ F ∘ₗ (Grass.line (A:=Letters d))
   have he : L (trow q p (i,k) u)=setas d (flora (Grass.atom l)):=by change setas d (F _)= _; rw [hF, ← hw]; cases q <;> rfl
   rw [←he]; apply Submodule.span_induction (p:=fun v _=>L v∈ O) ?_ (by simp) (fun _ _ _ _ h hp=> by rw [map_add]; exact (Pavilion H e b d).add_mem h hp) (fun _ _ _ h=>by rw [map_smul]; exact (Pavilion H e b d).smul_mem _ h) (twig_safe q (i,k) u b p) -- specify set
   rintro _ ⟨x,hx,rfl⟩; obtain ⟨w,hw,hW⟩:=circumvent e 0 x; let j:Barge:=⟨w,q,(i,k),u⟩
   have hm:j.pos=x:=hw; change setas d (F _ )∈ _; rw [hF,←hm]; exact buds H e b (.inr j) ⟨hW,(show j.pos≠b by rwa [hm])⟩
omit hp
include hp
lemma Wove (x:Labels.Key su) : setas d (coarse d (MvPolynomial.X x))∈ O := by
   let k:=d/2; obtain ⟨F,hF⟩:=coarseL (d:=d); by_cases h:2*Labels.generation x ≤ d; swap
   · have hQ:setas d (coarse d (MvPolynomial.X x))=0:=Subtype.ext ((lampT x d d).trans (if_neg h)); rw [hQ]; exact Submodule.zero_mem _
   let j:Fin (k-1):= ⟨x.1,(by unfold Labels.generation at h; unfold k; omega)⟩; let p: Pulled su k:= ((Labels.axes su j.val).coord x.2).comp (LinearMap.proj (φ:=fun i:Fin (k-1)=>Labels.Taylor su i.val) j); rw [literal_x, show literal _ = spell k p from (spell_explicit ..).symm]; have hg:= safe_span H (hp k) e p
   refine Submodule.span_induction (p:=fun q _=> setas d (coarse d (spell k q))∈ O) ?_ ?_ ?_ ?_ hg
   · rintro _ ⟨⟨v,i⟩,rfl⟩; exact buds H e b (.inl (v.val,i)) ⟨v.2,trivial⟩
   · rw [show spell k (0: Pulled su k)=0 from map_zero (spellMap su k),← hF, map_zero,map_zero]; exact Submodule.zero_mem _
   · intro u v _ _ hu hv; rw [show spell k (u+v)= _ from map_add (spellMap su k) _ _]; change setas d (coarse d (spell k u+spell k v))∈ _; rw [← hF,map_add,map_add,hF]; exact (Pavilion H e b d).add_mem hu hv
   intro c x _ he; rw [show spell k (c • x)=c • spell k x from map_smul (spellMap su k) _ _,show c • _=(c:ℂ) • spell k x from (IsScalarTower.algebraMap_smul ℂ c (spell k x)).symm,← hF,map_smul,map_smul,hF]; exact (Pavilion H e b d).smul_mem _ he
lemma foliage (p:Pol d): setas d p∈ O:=by
   induction p using TensorProduct.induction_on with
   | zero=>simp
   | tmul x y=>
       rw [combo]; apply pavilion_mul; swap
       · obtain ⟨F,hF⟩:=floraL (d:=d); have h(l:List (Letters d)): setas d (flora (l.map Grass.atom).prod)∈ O:=by
              induction l with
              | nil=> exact pavilion_one H e b
              | cons a l ih=> rw [List.map_cons,List.prod_cons,flora_at]; exact pavilion_mul _ _ _ _ _ (heights H e b a) ih
         rw [← Grass.write y,← hF,map_sum,map_sum]; apply Submodule.sum_mem; intro i _; obtain ⟨V,-,-,he⟩:=Grass.expression i; rw [map_smul,map_smul]; apply (Pavilion H e b d).smul_mem; rw [hF,he]; simpa only [List.map_ofFn] using h (List.ofFn V)
       obtain ⟨F,hF⟩:=coarseL (d:=d)
       induction x using MvPolynomial.induction_on with
       | C a=> rw [show MvPolynomial.C a=a • (1:gPoly) from by rw [MvPolynomial.smul_eq_C_mul,mul_one],← hF,map_smul,map_smul,hF]; exact (Pavilion H e b d).smul_mem _ (pavilion_one H e b)
       | mul_X a i h=>rw [coarse_at]; exact pavilion_mul _ _ _ _ _ h (Wove H hp e b i)
       | add x y hx hy=> rw [← hF,map_add,map_add,hF]; exact (Pavilion H e b d).add_mem hx hy
   | add x y hx hy=> rw [map_add]; exact (Pavilion H e b d).add_mem hx hy
end Arbitrary
variable (q: Reasons R H)
structure Tidy : Prop where
   gaugeSp (w:Point) (i:su.ColorIndex)(l:List Bough)(h:∀ k∈l,carat k w.e) : miniR d (glitter H w i d* canopy H d l) ∈ R
   spinSp (q:Bool)(i:Pinor)(k:Hue)(u:Flavor 6)(b:Cover)(l:List Bough)(h:∀ p∈l,vacant p b): miniR d (flora (Grass.line (Pulses.bent q i k u b))*canopy H d l) ∈ R
include hp
lemma suited (h:Tidy R H) :Reasons R H:=by
    have hv (p x:Pol d)(e:Edge Cover)(b:Cover)(hg:∀ l:List Bough,(∀ k∈l, permitted k e b) → miniR d (p*canopy H d l)∈R) : miniR d (p*x)∈ R:=by
       let L:= (miniR d).comp ((LinearMap.mulLeft ℂ p).comp (cap d).subtype); have he(q:Pol d): miniR d (p*q)=L (setas d q):=congr_arg (brighten d) (Subtype.ext (mulDry_right d d p q).symm)
       rw [he]; refine Submodule.span_induction (p:=fun q _=> L q∈R) ?_ (by simp) (fun u v _ _ h hh=>by rw [map_add]; exact R.add_mem h hh) (fun c p _ h=>by rw [map_smul]; exact R.smul_mem _ h) (foliage H hp e b x)
       rintro _ ⟨x,hx,rfl⟩; rw [←he]; exact hg x hx
    refine ⟨fun w i p=>hv _ _ w.e 0 (fun l hh=> h.gaugeSp w i l fun i he=>(hh i he).1), fun q i k u b p=>hv _ _ (0,0) b (fun l hh=>h.spinSp q i k u b l fun i he=>(hh i he).2)⟩
end SparK
end YM.Massive.Elm
#print axioms YM.Massive.Elm.SparK.suited
