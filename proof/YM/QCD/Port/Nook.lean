import YM.QCD.Port.Bench
/-! # prices exposure over incidence masks. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Port
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run Tree
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.Local
open Jets Sun Revolve Garden Bay Strut LeafM Paths Metric Extra AtomF Sway OrbitG ConnectedActivityE6 Push.AbsoluteSums Footprint Jets.Touch Pressure
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {f c:Side}{F:ℕ}{u v η ξ t p C D A R z q w γ Ω π κ B:ℝ}{b m i:ℕ}{j k:ℕ}{L:Flight j k}{J:Plan k}{H:f.val=c.val*L.L.val}{X:St f}{W:ℕ→Atom su 2}
local notation "Mx"=> Modes c F
local notation "S"=> sliceL L H
variable (P : Swathe L H X W J u v η p q b)
def broke (F m:ℕ)(i: Varn f c)(U:Grid f):EvenA c F:=exp (sliceF P F m i U)-1
def zoneG (U:Grid f)(i:Varn f c)(m:ℕ):Prop:= waxV i=none ∧ ¬ nearby U (orbitM S i) (m+1) B -- parameters S implicit notation won't elaborate F x
lemma fastR (x:ℝ)(hp:0≤x)(ht:x ≤ 1): Real.exp x-1 ≤ Real.exp 1*x:=by
   have hβ:=Real.add_one_le_exp (-x); rw [Real.exp_neg] at hβ; have hC:= mul_le_mul_of_nonneg_right hβ (Real.exp_pos x).le; rw [add_mul,inv_mul_cancel₀ (Real.exp_ne_zero x)] at hC; have hB:= mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ht) hp; linarith

-- Let η far cost h^2 φ high. choose Damage≥1. Exposure pieces.
structure RentP (P : Swathe L H X W J u v η p q b)(F m:ℕ)(t:ℝ)(z h Q:ℝ) : Prop where -- replace B
 profit :0<z
 growth :0<v
 toll :0 <h
 expR :∀ i,shells P F m h z i≤1
 always :1≤Q
 cap : Real.exp (max (F*AtomF.rays*2*q) (h^2*fingers F^2*(2*p))) ≤ Q*(Real.exp 1*z)
 hip:∀ i:Varn f c,waxV i=none→∀ U:Grid f,nearby U (orbitM S i) (m+1) t→ load (fun _=>h) (light _ (sliceF P F m i U))≤ z
 bend : 0≤η
variable {Z A : Type*}
lemma mountains (h:RentP P F m t z C w)(U:Grid f)(x:Varn f c):
  load (fun _=>C) (light _ (broke P F m x U)) ≤ if zoneG (B:=t) (L:=L) (H:=H) U x m then w*(Real.exp 1*shells P F m C z x) else Real.exp 1*shells P F m C z x:=by
    split
    next ht=>
     unfold shells; rw [if_pos ht.1]; exact ((Cove.bought _ _ _ (lux P F m U h.growth h.toll x)).trans ((sub_le_self _ zero_le_one).trans (Real.exp_le_exp.mpr (root_all P x ht.1 h.bend)))).trans h.cap
    next ht=>
      apply le_trans _ (fastR _ (by unfold shells; split; exact h.profit.le; exact grew P x h.growth h.toll) (h.expR x)); unfold shells; split
      next hh=> exact Cove.bought _ _ _ (h.hip _ hh U (by_contra fun he=> ht ⟨hh,he⟩))
      next hh=> exact Cove.bought _ _ _ (lux P F m U h.growth h.toll x)
-- for nearby Bad inventory, count per possible anchor, at most 2 variants per site. Ensure detection as contract

def rimP (T:Ratio c f)(B:ℕ)(x:Varn f c):Support f:=halo (B+1) (payT T B x)
lemma nearpath (x:Varn f c)(B:ℕ)(h:waxV x=none): halo (B+1) {orbitM S x}⊆ rimP S B x:=by
   exact Corona.halo_mono le_rfl (singleton_subset_iff.mpr (cared ..))

def spit (B : ℕ):ℕ:=2*((B+1)+(B+1)+1)^4
lemma insists (V:Grid f)(K:Finset (Varn f c))(D:Support f)(ht:∀ i ∈K,flags t V ∩ rimP S m i ⊆ D):
    (K.filter fun x=>zoneG (B:=t) (L:=L) (H:=H) V x m).card ≤ spit m * D.card:=by
   let p (i: Varn f c):=zoneG (B:=t) (L:=L) (H:=H) V i m; let C:=halo (m+1) D; let T:= K.filter p
   let a : Varn f c→ Bool:= fun x=> Sum.elim (fun _=> true) (fun _=>false) x
   let X i:= (a i, orbitM S i)
   have hy {u}(hh:u∈T):waxV u=none∧ orbitM S u∈C:=by
     have he:p u:=(mem_filter.mp hh).2
     obtain ⟨y,hY,hD⟩:= Finset.not_disjoint_iff.mp he.2
     obtain ⟨j,hj,h⟩:=halo_spec.mp hY; rw [mem_singleton.mp hj] at h
     exact ⟨he.1,halo_spec.mpr ⟨y, ht u (mem_filter.mp hh).1 (mem_inter.mpr ⟨hD,nearpath u m he.1 hY⟩), (separation_comm ..).trans_le h⟩⟩
   have he : T.card ≤ ((univ:Finset Bool) ×ˢ C).card := Finset.card_le_card_of_injOn X (fun u hu=>mem_product.mpr ⟨mem_univ _,(hy hu).2⟩) (fun i hi v hv hE => by
      have hh : orbitM S i= orbitM S v:= congr_arg Prod.snd hE; have hl:a i=a v:=congr_arg Prod.fst hE
      have he:= (hy hi).1; have hp:= (hy hv).1; rcases i with ⟨i,z⟩|⟨i,z⟩<;> rcases v with ⟨j,z'⟩|⟨j,z'⟩
      · change i=j at hh; change z=none at he; change z'=none at hp; rw [hh,he,hp]
      · contradiction
      · contradiction
      change (S).embed i=(S).embed j at hh; change z=none at he; change z'=none at hp; rw [(S).embed_injective hh,he,hp])
   refine he.trans ?_; rw [card_product,card_univ]; refine (Nat.mul_le_mul_left 2 (Corona.halo_size D _)).trans ?_; unfold spit; exact le_of_eq (by ring)

lemma proceeds (h:RentP P F m t z C w)(U:Grid f)(K:Finset (Varn f c))(V:Support f)(ht:∀ i∈K,flags t U ∩ rimP S m i ⊆ V):
   load (fun _=>C) (light _ (∏ x∈K,broke P F m x U)) ≤ w^(spit m * V.card)*∏ i∈K, (Real.exp 1*shells P F m C z i):=by
    apply (Cove.funded (fun _=>C) K _ _ (fun i _=> mountains P h U i)).trans; let q' i:= Real.exp 1* shells P F m C z i
    let p (i:Varn f c):=zoneG (B:=t) (L:=L) (H:=H) U i m
    have hi : 0 ≤ q':=fun i=> mul_nonneg (Real.exp_pos _).le (by unfold shells; split; exact h.profit.le; exact grew P i h.growth h.toll)
    change (∏ i∈K,if p i then w*q' i else q' i) ≤_
    rw [show (∏ i∈K,if p i then w*q' i else q' i)=(∏ i∈K, (if p i then w else 1)*q' i) from prod_congr rfl (fun i _=>by split<;> simp [*]), Finset.prod_mul_distrib,← prod_filter,prod_const]; exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ h.always (insists U K V ht)) (prod_nonneg fun i _=> hi i)
end YM.QCD.Port
