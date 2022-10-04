import React, {useEffect} from 'react'
import DataTable from 'react-data-table-component';
import CustomTable from "../../common-components/CustomTable";
import {Link} from "react-router-dom";
import fetchWrapper from "../../helpers/fetchWrapper";
import {CButton} from "@coreui/react";
import {swalConfirm, swalError, swalSuccess} from "../../helpers/common";


const Projects = () => {

    const [projects, setProjects] = React.useState([]);

    const fetchProjects = () => {
        fetchWrapper.get('/api/projects').then((response) => {
            const data = response.data;
            if (data.status === 'success') {
                setProjects(data.projects);
            }
        }).catch((error) => {

        });
    }

    const handleDelete = (id) => {
        swalConfirm().then((result) => {
            if (result.isConfirmed) {
                fetchWrapper.delete('/api/projects/' + id).then((response) => {
                    const data = response.data;
                    if (data.status === 'success') {
                        swalSuccess("Project deleted successfully");
                        fetchProjects();
                    } else {
                        swalError("Error deleting project");
                    }
                }).catch((error) => {
                    swalError("Error deleting project");
                });
            }
        });
    }

    const columns = [
        {
            name: 'PROJECTS',
            selector: row => row.project_name,
            sortable: true,
        },
        {
            name: 'SERVER ID',
            selector: row => row.server_id,
            sortable: true,
        },
        {
            name: 'CHANNEL IDS',
            selector: row => row.channels.map(channel => channel.channel_id).join(','),
            sortable: true,
        },
        {
            name: 'ACTIONS',
            selector: row => <div>
                <Link to={`/projects/${row.id}/edit`} className="btn btn-primary btn-sm">
                    <i className="fa fa-edit"></i>
                </Link>
                <CButton className="btn btn-danger btn-sm mx-2" onClick={() => handleDelete(row.id)}>
                    <i className="fa fa-trash"></i>
                </CButton>
            </div>,
        },
    ];

    useEffect(() => {
        fetchProjects();
    }, [projects.length]);

    return (
        <>
            <CustomTable title="Projects" columns={columns} data={projects} createLink="/projects/create" />
        </>
    )
}

export default Projects
