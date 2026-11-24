import YM.Elms.Blade
/-! # Measure individual scale-free cylinders in weight units of orientation ancestry.R -/
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
open Lining Lining.Temper Poised.Carte.Hem Permit
variable {n:Side}(U:Grid n)(P : Regulator n 6)
variable (o:Cover)(w v:Walk)(e:Point)(a:Axis)
namespace PrismD
variable (H: SourceRead.TaperHol)(K:Hol su)
open QCD.Kites Beacon -- glowing conflicts.
-- produce single projector independent of choices of enough size. Expose full motion
noncomputable abbrev TravelsP (X:Drape)(p:Mini d): Prop:=∃ M:ℕ, ∀ (n:Side)(o:Cover), M ≤ n.val→ ActionTest H o (X n o) p.val
def virtualP : BudgetPoint:=⟨2,6,1,1,1,le_rfl,le_rfl,by norm_num,by omega,by norm_num, le_rfl⟩
include K in
lemma peony(X:Drape)(g s d:ℕ)(h:Draft X g s):∃ p:Mini d, TravelsP H X p:=by
    obtain ⟨T,D,hD,hp,hQ⟩ : ∃ (T:Stenc)(D:Cylinder.Formula T 6), grant T D=X∧ (∀ i:Land,porch T i D∈layer (Pairs (Cylinder.Nearest T 6)) s) ∧ ∀ k m r:ℕ,used_bound T r→Lease r k m g (fun i=>porch T i D):= by obtain ⟨T,ht⟩:=h.exists; exact ⟨T,ht.funded⟩
    obtain ⟨r,hr⟩:=(Permit.eventual T).exists; let M:= 30*(r+2); have hM(X:Side)(he:M ≤ X.val): Merian.SmallT X T 0:=by intro u hu i; have h:=hr u hu i; unfold M at he; omega
    obtain ⟨t,ht,hT⟩:=hQ d virtualP.power r hr
    let n:Side:= ⟨M,by unfold M; positivity⟩
    let f :Land→ Dirac (Cylinder.Nearest T 6):=fun i=>porch T i D
    let F:=fun V:Grid n=> f (expandAt (wrap n (0:Cover)) V)
    let Φ:=(tongue (c:=n) T (0:Cover)).toLinearMap.toContinuousLinearMap.restrictScalars ℝ; have hF : ContDiffAt ℝ d (F∘increment (1: Grid n)) 0:=by
        have h:2*(r+1)< n.val:=by change 2*(r+1)<M; unfold M; omega
        have hl:= (hT virtualP n (wrap n (0:Cover)) h rfl).smooth [] (Nat.zero_le d) (1:Grid n)
        exact hl.contDiffAt.of_le (by norm_cast; simp)
    have hx : ⇑(X n 0)=Φ ∘ F:= by rw [←hD]; exact funext fun U=>granting ..
    obtain ⟨y,hy,hV⟩:= Beacon.obtainsD (d:=d) H 0 (X n 0) (by rw [hx]; exact Φ.contDiff.contDiffAt.comp (f:=F∘increment (1:Grid n)) (0:Directions su n) hF); refine ⟨⟨y,hy⟩,M,fun N o hN J=>?_⟩; specialize hV J
    have hX(N:Side)(o:Cover)(hz:M≤N.val): moment (c:=N) (d:=d) H o J (X N o) = SourceRead.onStencil K D d J:=by rw [← hD]; exact funext fun t=>Merian.exact_placement H K N o T D (hM N hz) ..
    rw [hX N o hN, ← hX n 0 le_rfl]; exact hV
lemma convoy {g s:ℕ}{X:Drape}(h:Draft X g s) (A:Grid n) (o:Cover): X n o A∈ Grass.layer (Pairs (Modes n 6)) s:=by obtain ⟨S,hs⟩:=h.exists; obtain ⟨F,rfl,hp,-⟩:=hs.funded; rw [granting]; exact Grass.exterior_layer _ (hp _)
-- extracted debit using one radius set.Clock.G.Unit. 
structure Survey (X:Drape)(g s:ℕ)(p:Mini d) : Prop where
    paid : Draft X g s
    grantX :∃ y:Mini d, TravelsP H X y ∧ Tendsto (fun t:ℝ=> ((↑(t^g):ℂ))⁻¹ • prism t 1 d y) (𝓝[>] 0) (𝓝 p)
lemma lumP (d:ℕ)(x:Mini d) (t v:ℝ): Continuous (fun t=> prism t v d x):=by
    refine continuous_iff_continuousAt.mpr fun t=> tint_heights (Y:=fun t=>prism t v d x) ?_; intro J; simp_rw [measures]
    have he:Continuous (fun t:ℝ=> ready d J (widths t v x.val)):=by rw [← (zBasis d).linearCombination_repr x.val]; simp_rw [Finsupp.linearCombination_apply,Finsupp.sum,map_sum,map_smul,minted,widths_m,map_smul]; fun_prop
    exact he.tendsto t
include K in
lemma zeroFund (X:Drape)(s d:ℕ)(hh:Draft X 0 s): ∃ p:Mini d,Survey H X 0 s p:=by
    obtain ⟨p,hp⟩:= peony H K X 0 s d hh; refine ⟨prism 0 1 d p, hh,p,hp,?_⟩; simp_rw [pow_zero,Complex.ofReal_one,inv_one,one_smul]; exact ((lumP d p 0 1).tendsto _).mono_left nhdsWithin_le_nhds
variable {H}
lemma Survey.add {X Y:Drape}{g s:ℕ}{x y:Mini d}(h:Survey H X g s x)(hp:Survey H Y g s y): Survey H (X+Y) g s (x+y):=by
   obtain ⟨p,⟨N,hP⟩,he⟩:=h.grantX; obtain ⟨q,⟨M,hM⟩,hQ⟩:=hp.grantX; refine ⟨h.paid.joins hp.paid,p+q, ⟨N+M,fun n o hn=> plusA o H _ _ _ _ (hP n o (by omega)) (hM n o (by omega))⟩, ?_⟩ -- sig v
   simp_rw [map_add, smul_add]; exact he.add hQ
lemma Survey.mul {X Y:Drape}{g s k m:ℕ}{x y:Mini d}(h:Survey H X g s x)(hp:Survey H Y k m y): Survey H (X*Y) (g+k) (s+m) (foldP d x y):=by
   obtain ⟨p,⟨N,hP⟩,he⟩:=h.grantX; obtain ⟨q,⟨M,hM⟩,hQ⟩:=hp.grantX; refine ⟨h.paid.mulX hp.paid,foldP d p q, ⟨N+M,fun n o hn=> mulA o H _ _ _ _ (hP n o (by omega)) (hM n o (by omega))⟩,?_⟩
   have ht:=foldH _ _ _ _ _ he hQ; simp_rw [fold_scale] at ht; simp_rw [pow_add, Complex.ofReal_mul,mul_inv,prism_fold]; exact ht
lemma Survey.scale {X:Drape}{g s:ℕ}{x:Mini d}(h:Survey H X g s x)(u:ℂ): Survey H (u • X) g s (u • x):=by
   obtain ⟨p,⟨N,hP⟩,he⟩:=h.grantX; refine ⟨h.paid.scale _,u • p,⟨N,fun n o hn=>constA o H u _ _ (hP n o hn)⟩,?_⟩; have hf:= he.const_smul u; simp_rw [map_smul,smul_comm _ u]; exact hf
lemma Survey.neg {X:Drape}{g s:ℕ}{x:Mini d}(h:Survey H X g s x): Survey H (-X) g s (-x):=by simpa using h.scale (-1)
lemma Survey.sub {X Y:Drape}{g s:ℕ}{x y:Mini d}(h:Survey H X g s x)(hp:Survey H Y g s y): Survey H (X-Y) g s (x-y):=by rw [sub_eq_add_neg,sub_eq_add_neg]; exact h.add hp.neg
variable (H)
lemma Survey.dry (g s d:ℕ): Survey H 0 g s (0:Mini d):=by
   refine ⟨drought ..,0, ⟨0,fun n o _ J=>?_⟩,?_⟩
   · change SourceRead.Agrees (moment H o J (0: Density n 6)) (SourceRead.desired (0:Pol d) J); simp_rw [show moment H o (d:=d) J (0:Grid n→Lat.Fields n 6)= 0 from funext fun i=>map_zero (adapter ..), ← funext (observe J (0:Pol d)), map_zero] -- needs rfl.Go
     exact ⟨contDiffAt_const,contDiffAt_const,fun _ _=> rfl⟩
   simp
lemma Survey.total {ι:Type} (g s d:ℕ)(x:Finset ι)(V:ι→ Drape)(P:ι→Mini d)(hp:∀ i∈x, Survey H (V i) g s (P i)): Survey H (∑ i∈x,V i) g s (∑ i∈x,P i):=by
    induction x using Finset.induction_on with
    | empty => rw [sum_empty,sum_empty]; exact Survey.dry ..
    | insert i x hi hx=> rw [sum_insert hi,sum_insert hi]; exact (hp _ (mem_insert_self ..)).add (hx (fun i h=>hp _ (mem_insert_of_mem h)))
end PrismD
end Arbor
end SparK
end YM.Massive.Elm
#print axioms YM.Massive.Elm.SparK.Arbor.PrismD.peony
