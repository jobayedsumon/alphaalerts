import React from 'react'
import { Navigate} from 'react-router-dom'
import {
    CButton,
    CCol,
    CContainer,
    CForm,
    CFormInput, CImage,
    CInputGroup,
    CRow,
} from '@coreui/react'
import {isLoggedIn, login, walletConnect} from "../../../helpers/authHelper";
import {swalError} from "../../../helpers/common";
import {useDispatch} from "react-redux";
import fetchWrapper from "../../../helpers/fetchWrapper";
import logo from "../../../assets/images/logo.png";

const Login = () => {

    const dispatch = useDispatch();

    const walletConnectHandler = (e) => {
        e.preventDefault();
        walletConnect().then(response => {
            if (response && response.user && response.token) {
                fetchWrapper.defaults.headers.common['Authorization'] = 'Bearer ' + response.token;
                dispatch({type: 'set', user: response.user, token: response.token});
            }
        }).catch(error => {
            swalError("Error connecting wallet");
        })
    }

    const handleSubmit = (e) => {
        e.preventDefault()
        const email = e.target.email.value;
        const password = e.target.password.value;
        login(email, password).then(response => {
                if (response && response.user && response.token) {
                    fetchWrapper.defaults.headers.common['Authorization'] = 'Bearer ' + response.token;
                    dispatch({type: 'set', user: response.user, token: response.token});
                }
            }
        ).catch(error => {
                swalError("Error logging in");
            }
        );
    }

    return (
        isLoggedIn() ? <Navigate to="/" replace/> :
            <div className=" min-vh-100 d-flex flex-row align-items-center loginPage">
                <CContainer>

                    <CRow className="justify-content-center align-items-center">

                        <CCol md={6} className="text-center">
                            <CImage src={logo} width={100} />
                            <CForm onSubmit={handleSubmit}>
                                <h1 className="text-white text-center">Alpha Alerts</h1>
                                <CInputGroup className="mb-3">
                                    <CFormInput type="email" placeholder="Email" name="email"/>
                                </CInputGroup>
                                <CInputGroup className="mb-4">
                                    <CFormInput
                                        type="password"
                                        placeholder="Password"
                                        name="password"
                                    />
                                </CInputGroup>
                                <CInputGroup className="d-flex justify-content-between align-items-center">
                                    <CButton className="loginButtons" type="submit">Login</CButton>
                                    <h6 className="text-white">Or</h6>
                                    <CButton className="loginButtons" onClick={walletConnectHandler}>Connect Wallet</CButton>
                                </CInputGroup>
                            </CForm>
                        </CCol>
                    </CRow>
                </CContainer>
            </div>
    )
}

export default Login
