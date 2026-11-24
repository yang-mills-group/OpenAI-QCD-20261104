import YM.Tinus.Beta
set_option autoImplicit false
noncomputable section
namespace YM.Intag
open Function Filter
-- LET Receipt numerical safe.P1. αShip. choose C after L fixed before x. G cost poly in log/time. H0 and motors then.
namespace Receipt
variable {T G V0 V1 r α a β φ D b c W Ξ:ℝ}
local notation "K"=> T^10
noncomputable def motor (G T:ℝ) :ℝ:= (|G|+1)*T^10
local notation "M"=> motor G T
local notation "X1"=> T*M
local notation "X2"=> T*(T*M)
noncomputable def cropE (G T:ℝ) :ℝ:= motor G T * T^22
local notation "Y"=> cropE G T
local notation "λℓ"=>V0/M
local notation "λφ"=> V0/Y
local notation "R0"=>V0/K
-- r:pL≥0 and ≤1/Cs, α:Πv M.K Θ clock.A. reindex parameters later.Ph. EG next, θK=T^
set_option quotPrecheck false
variable (hT:8≤ T)(hV:0< V0)(hA:V1 ≤4*V0)(hB: V0≤ 4*V1)
structure Prosper (V0 V1 T G a b D c r α β W φ:ℝ) : Prop where
    peaks : V0/T^10 ≤ V1
    motion : V0/motor G T * G ≤ V0/T^10
    honour : a*(b*(V0/T^10)+ (D*(V0/T^10)+r*V1)) ≤ V0
    credit : r*V1+c*(V0/T^10)≤ V0
    useMt : α* motor G T ≤ cropE G T
    merit : α* motor G T ≤ T*motor G T
    lens: β* (T* motor G T) ≤ T*(T*motor G T)
    wind: V0/cropE G T * W * (T*(T*motor G T))+ V0/cropE G T * G ≤ V0/T^10
    runway: V0/cropE G T *G ≤ V0/T^10
    leaves: V0/cropE G T * (T*(T*motor G T)) ≤ V1
    oldBil: V0/cropE G T * φ * (T*(T*motor G T)) ≤ V1
include hT hV hA hB
set_option maxHeartbeats 680000 in
lemma florist (hL:0 ≤ a)(ha:a≤ T)(hb:b ≤ T)(hd:D ≤ T)(hc:c≤ T*T)(hR:0 ≤ r)(hq:r≤ 1/K)(hα:α≤T)(hW:W≤ T)(hβ:β≤ T)(hf: φ≤ T): Prosper V0 V1 T G a b D c r α β W φ:=by
      have ht: 1 ≤ T:= le_trans (by norm_num) hT; have hT':0<T:= lt_of_lt_of_le zero_lt_one ht; let x:=K; let u:= R0; have hu:0<u:=div_pos hV (pow_pos hT' _); have hM:0<M:=by unfold motor; positivity
      have hC:4 < x:= lt_of_lt_of_le (by linarith : 4 < T) (le_self_pow₀ ht (by norm_num)); have hY:0<Y:= by unfold cropE; positivity
      have heS:u*x= V0:= div_mul_cancel₀ _ (pow_pos hT' _|>.ne'); have hp:u≤ V1:=(div_le_iff₀ (by positivity)).2 (hB.trans ((mul_le_mul_of_nonneg_right hC.le (by linarith only [hB,hV])).trans_eq (mul_comm ..)))
      have hΓ: r*V1 ≤ 4*u:= (mul_le_mul_of_nonneg_left hA hR).trans ((mul_le_mul_of_nonneg_right hq (by positivity)).trans_eq (by unfold u; field_simp))
      have hcM: 6*T^2 ≤ x:=by have h: T^3 ≤ x:=pow_le_pow_right₀ ht (by norm_num : 3 ≤ 10); refine le_trans ?_ h; nlinarith only [sq_nonneg T,mul_le_mul_of_nonneg_right hT (sq_nonneg T)]
      have hv :4*T*u ≤ 4*T^2*u:= mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_self_pow₀ ht (by norm_num)) (by norm_num)) hu.le
      have hz :u*(2*T*T)+u*4*T≤ V0:=by rw [←heS]; nlinarith only [hv,mul_le_mul_of_nonneg_right hcM hu.le]
      have hQ: T ≤ T^22:=le_self_pow₀ ht (by norm_num); have heG: G ≤ M:= le_trans (le_trans (le_abs_self _) (by linarith: |G|≤ |G|+1)) (le_mul_of_one_le_right (by positivity) (one_le_pow₀ ht))
      have hhG: λℓ*G≤u:= by refine (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (le_add_of_nonneg_right zero_le_one)) (by positivity : 0 ≤ V0/M)).trans_eq ?_; unfold motor u; field_simp
      have hx: X2 ≥0:=by positivity
      have hCost: λφ*T*X2+ λφ*M ≤ u:=by
           unfold u; -- At * affect hu arith.
           rw [show V0/Y*T*X2+V0/Y*M=V0/Y* M*(T^3+1) by ring, cropE]; field_simp
           nlinarith only [one_le_pow₀ ht (n:=3), (mul_le_mul_of_nonneg_right hT (pow_nonneg hT'.le 3)),pow_le_pow_right₀ ht (by norm_num : 4 ≤ 12)]
      have hXs :λφ*T*X2 ≤ u:= (le_add_of_nonneg_right (by positivity)).trans hCost
      refine ⟨hp,hhG,?_,?_ , (mul_le_mul_of_nonneg_right (le_trans hα hQ) hM.le).trans_eq (mul_comm ..),mul_le_mul_of_nonneg_right hα hM.le,mul_le_mul_of_nonneg_right hβ (by positivity), (add_le_add (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW (by positivity)) hx) (mul_le_mul_of_nonneg_left heG (by positivity))).trans hCost,(mul_le_mul_of_nonneg_left heG (by positivity)).trans ((le_add_of_nonneg_left (by positivity)).trans hCost),((mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by positivity) ht) hx).trans hXs).trans hp, ((mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf (by positivity)) hx).trans hXs).trans hp⟩
      · have hZ:0≤ T*u+(T*u+4*u):=by positivity
        have h: b*u+(D*u+r*V1) ≤ T*u +(T*u+4*u):=add_le_add (mul_le_mul_of_nonneg_right hb hu.le) (add_le_add (mul_le_mul_of_nonneg_right hd hu.le) hΓ)
        exact (mul_le_mul_of_nonneg_left h hL).trans ((mul_le_mul_of_nonneg_right ha hZ).trans ((le_of_eq (by ring)).trans hz))
      have hh:1≤T^2:=one_le_pow₀ ht
      refine (add_le_add hΓ (mul_le_mul_of_nonneg_right hc hu.le)).trans ?_; linarith only [hz,mul_nonneg hu.le (show 0≤T*T from mul_nonneg hT'.le hT'.le),mul_le_mul_of_nonneg_left ht hu.le] -- psts
end Receipt
end YM.Intag
#print axioms YM.Intag.Receipt.florist
