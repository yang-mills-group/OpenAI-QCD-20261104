import YM.Mako.Kick
set_option maxHeartbeats 440000
set_option autoImplicit false
noncomputable section
namespace YM.Mako
open Function Filter Set Polynomial
open scoped Topology BigOperators Classical
open Module
variable {W:Type*}[AddCommGroup W][Module ℂ W][FiniteDimensional ℂ W]
local notation "M"=> Module.End ℂ W
variable {H E F: Module.End ℂ W}
-- Poly(P)
namespace Links
variable (h:Links H E F)(hc:Clear H)
include h hc
lemma bothN :∃ N:ℕ,E^(N+1)=0∧F^(N+1)=0:=by
    obtain ⟨n,hn⟩:= h.silenced hc; obtain ⟨j,hj⟩:=h.undone hc; refine ⟨n+j,?_,?_⟩
    · rw [show n+j+1=n+1+j by omega,pow_add,hn,zero_mul]
    rw[show n+j+1=j+1+n by omega,pow_add,hj,zero_mul]
lemma creates: ∃ p:Module.End ℂ W, Split p {H,E,F} :=by
     obtain ⟨n,hn,hN⟩:= h.bothN hc
     let Q:= Lace.credit hc; let L:= aeval H Q.poly; let P:= pledge E F n; let T:=P*L
     have he(x:W): E (T x)=0:=by change E (pledge E F n (L x))=0; rw[h.cat _ (Q.zero x),hn,LinearMap.zero_apply,map_zero,smul_zero]
     have hv(x:W): H (T x)=0:= h.diving _ (Q.zero x) n
     have hf(x:W): F (T x)=0:= h.f_kill hc (T x) (he _) (hv _) -- x should T x
     have hΛ (x:W)(a:ℂ)(h:H x=a • x)(ha:a≠0):T x=0:=by change P (aeval H Q.poly x)= _; rw [Q.smite a x h ha,map_zero]
     obtain ⟨B,a,ha⟩:= (show Clear H from hc)
     have hush:T*H=0:=by
         refine B.ext fun i=>?_ ; rw [End.mul_apply,ha,map_smul]; by_cases ht:a i=0; · simp [ht]
         rw [hΛ _ _ (ha i) ht,smul_zero]; rfl
     have fund:T*F=0:=by
           refine B.ext fun i=>?_ ; let x:= B i; have ht:=h.fur _ _ (ha i) 1
           change T (F (B i))=0; have hp:H (F (B i))=(a i-2) • F (B i):=by simpa using ht
           by_cases hv:a i= 2
           · change P (aeval H Q.poly (F (B i)))=0; rw [Q.fixes _ (by rw [hp,hv,sub_self,zero_smul])]; unfold P; rw[h.cour _ (by rw [ha,hv]),hN, LinearMap.zero_apply,smul_zero]
           exact hΛ _ _ hp (sub_ne_zero.mpr hv)
     have endo:T*E=0:=by
           refine B.ext fun i=>?_ ; have hp:= ha i; have hv:= h.etch _ _ hp; change T (E (B i))=0; by_cases hc':a i+2=0
           · obtain ⟨v,hj,hy⟩:= h.covered hc (B i) (by rw [eq_neg_of_add_eq_zero_left hc'] at hp; exact hp)
             rw[hy, show E (F v)= F (E v) from ?_]; exact DFunLike.congr_fun fund (E v)
             apply sub_eq_zero.mp; change (E*F-F*E) v=0; rw[h.ef,hj]
           exact hΛ _ _ hv hc'
     let C:Set M:={H,E,F}; refine ⟨T, {hit:=?_,gun:=?_,budget:=?_}⟩
     · intro i h; rcases (show i=H ∨ i=E ∨ i=F from by simpa using h) with rfl|rfl|rfl <;> first|(exact LinearMap.ext hv)|(exact LinearMap.ext he)|(exact LinearMap.ext hf)
     · intro i h; rcases (show i=H ∨ i=E ∨ i=F from by simpa using h) with rfl|rfl|rfl <;> assumption
     have blast(i:ℕ):Fet C (pledge E F i-1):=by
           induction i with
           | zero=>rw [pledge,sub_self]; exact Fet.zero
           | succ i ih=>
               rw [pledge,add_comm, add_sub_assoc]; exact Fet.add _ _ (Fet.smul _ _ (Fet.times _ _ ((Fet.mem _ (show F∈C from by simp[C])).pow' i) ((Fet.mem _ (show E∈C from by simp[C])).pow' i))) ih
     exact Fet.products (blast n) ((Fet.mem H (show H∈C from by simp[C])).pose Q)
end Links
variable {C D:Set (Module.End ℂ W)} {k l:Module.End ℂ W} -- use explicit
namespace Fet
lemma suburb : Submodule.span ℂ C = Submodule.span ℂ D →∀ x:End ℂ W,Fet C x→ Fet D x:=by
     intro h x HX; induction HX with
     | mem i hi =>
          have hm: i∈ Submodule.span ℂ D:= h ▸ Submodule.subset_span hi
          exact Submodule.span_induction (p:= fun k _=>Fet D k) (fun i hi=> mem i hi) zero (fun x y _ _=> add _ _) (fun a x _=> smul _ _) hm
     | zero=>exact zero
     | times x y _ _ h h'=>exact times _ _ h h'
     | add x y _ _ h h'=>exact add _ _ h h'
     | smul a x _ h=>exact smul _ _ h
end Fet
namespace Split
variable (x y: Module.End ℂ W)
lemma joins (h:Split x C)(he:Split y D)(hv:∀ i∈C,∀ j∈D, Commute i j): Split (x*y) (C∪D):=by
    refine ⟨?_,?_, Fet.products (h.budget.mono (subset_union_left)) (he.budget.mono (subset_union_right))⟩
    · intro z hz; rcases hz with hz|hz; · rw [←mul_assoc,h.hit z hz,zero_mul]
      rw [← mul_assoc,(h.budget.stamp (fun i H=> (hv i H z hz).symm)).eq,mul_assoc,he.hit z hz,mul_zero]
    intro z hz; rcases hz with hz|hz; · rw [mul_assoc, ←(he.budget.stamp (hv z hz)).eq, ←mul_assoc,h.gun z hz,zero_mul]
    rw[mul_assoc,he.gun z hz,mul_zero]
lemma home (h:Split x C)(ht:Submodule.span ℂ C= Submodule.span ℂ D): Split x D:=by
     refine ⟨?_,?_,Fet.suburb ht _ h.budget⟩
     · intro i hi; let P:Submodule ℂ M:=LinearMap.ker (LinearMap.mulRight ℂ x); have hp: Submodule.span ℂ C≤ P:= Submodule.span_le.mpr (fun q hq=> h.hit q hq); exact hp (ht.symm ▸ Submodule.subset_span hi)
     intro i hi; let P:Submodule ℂ M:=LinearMap.ker (LinearMap.mulLeft ℂ x); have hp: Submodule.span ℂ C≤ P:= Submodule.span_le.mpr (fun q hq=> h.gun q hq); exact hp (ht.symm ▸ Submodule.subset_span hi)
end Split
end YM.Mako
#print axioms YM.Mako.Links.creates
#print axioms YM.Mako.Split.joins
#print axioms YM.Mako.Split.home
